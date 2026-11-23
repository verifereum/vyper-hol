(* Evaluate the screen's predicates on generated units; one TSV row each.

   (a) acceptance: check_contract T and F, exports_ok, layouts agreement.
   (b) the executable contract_inv groups 1-4, in each mode.
   (c) for accepted units: compile_vyper_mods asm_opt_finalizer, deploy and
       one call on the EVM and on the interpreter, compared. *)
structure linkedScreenRun = struct

open HolKernel boolLib bossLib linkedScreenDefsTheory

fun tm s = Parse.Term [QUOTE s]

fun secs t0 = Real.fmt (StringCvt.FIX (SOME 2)) (Time.toReal (Time.- (Time.now (), t0)))

(* Result of a conversion as a short word: T, F, or err:<message>. *)
fun truth conv t = let
    val r = rhs (concl (conv t))
  in if Teq r then "T" else if Feq r then "F" else "open"
  end handle e => "err:" ^ General.exnMessage e

val tenv_free_ids = map (fn n => let
    val g = tm ("!tenv. vyperABIEntries$abi_method_id tenv \"" ^ n ^ "\" [] = " ^
                "vyperABIEntries$abi_method_id FEMPTY \"" ^ n ^ "\" []")
  in TRANS (SPEC_ALL (prove (g, simp[vyperABIEntriesTheory.abi_method_id_def,
                                    vyperABITheory.vyper_to_abi_type_def])))
           (cv_transLib.cv_eval (tm ("vyperABIEntries$abi_method_id FEMPTY \"" ^ n ^
                                     "\" []")))
  end handle e => (print ("selector " ^ n ^ ": " ^ General.exnMessage e ^ "\n");
                   TRUTH)) ["f", "entry", "x", "__default__", "g", "s"]

val () = computeLib.add_funs (List.filter (fn th => not (Teq (concl th))) tenv_free_ids)

(* Every selector the units can ask for, so EVAL never hashes. *)
val selector_names = ["f", "entry", "x", "__default__", "g", "s", "gsf", "tgeo",
                      "zzz", "__init__", "c", "y"]
val () = computeLib.add_funs (List.concat (map (fn n =>
    map (fn args => cv_transLib.cv_eval (tm ("function_selector \"" ^ n ^ "\" " ^ args)))
      ["[]", "[Uint 256]", "[Uint 8]"]) selector_names))

(* The type-env selector collision pair, with their struct arguments
   resolved and unresolved. *)
val () = computeLib.add_funs (List.concat (map (fn n =>
    map (fn args => cv_transLib.cv_eval (tm ("function_selector \"" ^ n ^ "\" " ^ args)))
      ["[Tuple [Uint 256]]", "[Tuple [Uint 8]]", "[Tuple []]"]) ["q21f9b", "q25078"]))

fun check_conv d lay mods = let
    val t = tm ("vyperTypeContract$check_contract " ^ d ^ " [(2w:address, " ^ lay ^
                ")] 2w " ^ mods)
    val r = rhs (concl (vyperCheckContractLib.check_contract_conv t))
  in if optionSyntax.is_some r then "T" else if optionSyntax.is_none r then "F"
     else "open"
  end handle e => "err:" ^ General.exnMessage e

(* imm_len_mods is [nocompute]; unfold it before evaluating. *)
fun exec_conv exec_thm =
  REWR_CONV exec_thm THENC PURE_REWRITE_CONV [bodyInvSplitTheory.imm_len_mods_def] THENC
  EVAL

fun groups d lay mods exps = [
  truth (exec_conv screen_g1_exec) (tm ("screen_g1 " ^ d ^ " " ^ mods ^ " " ^ exps)),
  truth (exec_conv screen_g2_exec)
    (tm ("screen_g2 " ^ d ^ " " ^ lay ^ " " ^ mods ^ " " ^ exps)),
  truth (exec_conv screen_g3_exec) (tm ("screen_g3 " ^ d ^ " " ^ lay ^ " " ^ mods)),
  truth (exec_conv screen_g4_exec) (tm ("screen_g4 " ^ d ^ " " ^ lay ^ " " ^ mods))]

val compile_rule = CONV_RULE (RAND_CONV
  (PURE_ONCE_REWRITE_CONV [GSYM wordsTheory.n2w_mod] THENC
   DEPTH_CONV wordsLib.SIZES_CONV THENC numLib.REDUCE_CONV))

fun hm_slots () = map (fn s => let
    val r = rhs (concl (EVAL (tm (
      "w2n (THE (compute_hashmap_slot (n2w " ^ Int.toString s ^ ") [" ^
      "BaseT (UintT 256)] [ValueSubscript (IntV 1)]))"))))
  in Arbnum.toString (numSyntax.dest_numeral r) end
  handle e => (print ("hashmap slot: " ^ General.exnMessage e ^ "\n"); "0"))
  [10, 11]

val hm_slot_strs = ref (NONE : string list option)
fun ks_of hm = let
    val extra = if hm then (case !hm_slot_strs of
                              SOME l => l
                            | NONE => let val l = hm_slots () in
                                        hm_slot_strs := SOME l; l end)
                else []
  in "[0; 1; 10; 11" ^ String.concat (map (fn s => "; " ^ s) extra) ^ "]" end

fun term_str t = let
    val s = term_to_string t
  in String.translate (fn #"\n" => " " | #"\t" => " " | c => String.str c) s end

(* (c): compile, then deploy and call on both sides. *)
fun run_c (u : linkedScreenGen.unit_spec) lay = let
    val ct = tm ("compile_vyper_mods asm_opt_finalizer (o1_policy all_capabilities) " ^
                 #mods u ^ " " ^ #exps u)
    val r = rhs (concl (compile_rule (EVAL ct)))
  in
    if optionSyntax.is_none r then ["compile_NONE", "", "", "", ""]
    else if not (optionSyntax.is_some r) then ["compile_open", "", "", "", ""]
    else let
      val (dbc, _) = pairSyntax.dest_pair (optionSyntax.dest_some r)
      val data = rhs (concl (cv_transLib.cv_eval (tm (
        "function_selector \"" ^ #sel u ^ "\" []"))))
      val ks = tm (ks_of (#hm u))
      val evm = rhs (concl (cv_transLib.cv_eval (list_mk_comb (
        prim_mk_const {Thy = "linkedScreenDefs", Name = "screen_evm_run"},
        [dbc, data, ks]))))
    in
      if optionSyntax.is_none evm then ["compiled", "evm_no_end", "", "", ""] else let
        val evm_parts = pairSyntax.strip_pair (optionSyntax.dest_some evm)
        val code = List.nth (evm_parts, 2)
        val src = rhs (concl (cv_transLib.cv_eval (list_mk_comb (
          prim_mk_const {Thy = "linkedScreenDefs", Name = "screen_src_run"},
          [tm lay, tm (#mods u), tm (#exps u), dbc, stringSyntax.fromMLstring (#fname u),
           data, code, tm (#rt u), ks]))))
        val src_parts = pairSyntax.strip_pair src
        (* evm: deploy_ok, dep_slots, code, call_ok, rdata, call_slots
           src: deploy_ok, dep_slots, call_ok, bytes option, call_slots *)
        val e = fn n => List.nth (evm_parts, n)
        val s = fn n => List.nth (src_parts, n)
        val src_bytes = s 3
        val bytes_agree =
          if optionSyntax.is_some src_bytes
          then aconv (optionSyntax.dest_some src_bytes) (e 4)
          else Teq (e 3) andalso false
        val deploy_agree = aconv (e 0) (s 0) andalso
                           (Feq (e 0) orelse aconv (e 1) (s 1))
        val call_agree = Feq (e 0) orelse
          (aconv (e 3) (s 2) andalso aconv (e 5) (s 4) andalso
           (bytes_agree orelse (Feq (e 3) andalso optionSyntax.is_none src_bytes)))
      in ["compiled", if deploy_agree then "T" else "F",
          if call_agree then "T" else "F",
          "evm:" ^ term_str (e 0) ^ "," ^ term_str (e 3) ^ "," ^ term_str (e 5) ^
            ",ret=" ^ term_str (e 4),
          "src:" ^ term_str (s 0) ^ "," ^ term_str (s 2) ^ "," ^ term_str (s 4) ^
            ",ret=" ^ term_str (s 3)]
      end
    end
  end handle e => ["c_err:" ^ General.exnMessage e, "", "", "", ""]

val header = ["id", "site", "vis", "place", "qualifier", "qual_rel", "presence",
  "target_declared", "target_alloc", "kind",
  "checkT", "checkF", "exports_ok", "layouts_agree", "accepted",
  "g1F", "g2F", "g3F", "g4F", "g1T", "g2T", "g3T", "g4T",
  "compile", "deploy_agree", "call_agree", "evm", "src", "secs_ab", "secs_c"]

fun run_unit with_c (u : linkedScreenGen.unit_spec) = let
    val t0 = Time.now ()
    val lay = "(" ^ #sl u ^ ", " ^ #tl u ^ ")"
    val ckT = check_conv "T" lay (#mods u)
    val ckF = check_conv "F" lay (#mods u)
    val ex = truth EVAL (tm ("exports_ok [(2w:address, " ^ lay ^ ")] 2w " ^
                             #mods u ^ " " ^ #exps u))
    val la = truth (exec_conv screen_layouts_agree_exec)
               (tm ("screen_layouts_agree " ^ #mods u ^ " " ^ #exps u ^ " " ^ lay))
    val acc = List.all (fn x => x = "T") [ckT, ckF, ex, la]
    val bF = groups "F" lay (#mods u) (#exps u)
    val bT = groups "T" lay (#mods u) (#exps u)
    val tab = secs t0
    val t1 = Time.now ()
    val c = if acc andalso with_c then run_c u lay else ["", "", "", "", ""]
    val tc = if acc andalso with_c then secs t1 else ""
  in
    [#id u] @ map #2 (#axes u) @ [ckT, ckF, ex, la, if acc then "T" else "F"] @
    bF @ bT @ c @ [tab, tc]
  end

fun clean s = String.translate (fn #"\t" => " " | #"\n" => " " | c => String.str c) s
fun row fields = String.concatWith "\t" (map clean fields) ^ "\n"

(* Run units k, k+n, k+2n, ... of the list, appending rows to path. *)
fun run_slice with_c units k n path = let
    val out = TextIO.openAppend path
    fun go _ [] = ()
      | go j (u :: us) =
          (if j mod n = k then
             (TextIO.output (out, row (run_unit with_c u)); TextIO.flushOut out)
           else ();
           go (j + 1) us)
  in go 0 units; TextIO.closeOut out end

end
