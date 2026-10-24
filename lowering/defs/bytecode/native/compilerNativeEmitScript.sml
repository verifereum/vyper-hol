(*
 * Build-time generator for the native (unchecked) bytecode parity runner.
 *
 * Exports, through EmitML's printer, the equations that EVAL uses for
 * compile_vyper and the parity fixture programs, so the same equations run as
 * compiled Standard ML.  Nothing here produces a theorem: the generated code is
 * trusted, not kernel-checked.  See README.md in this directory.
 *)
Theory compilerNativeEmit
Ancestors compileVyper evalCompiler evalCompilerSubsetAbiBuiltins evalCompilerSubsetAbiEvents
  evalCompilerSubsetAbiExternalCalls evalCompilerSubsetAbiExternal evalCompilerSubsetAbiInternalCalls
  evalCompilerSubsetBuiltins evalCompilerSubsetControlDeploy evalCompilerSubsetScalars evalCompilerSubsetState
  integer_word alist
Libs EmitML finite_mapLib wordsLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY]);
val () = computeLib.upd_compset (computeLib.add_thms [integer_wordTheory.i2w_pos]);

(* Static annotation read by holbuild; a no-op when the script runs. *)
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_outputs ["compilerNativeML.sml"];

val module_name = "compilerNative";
fun pr s = TextIO.print s;

(* ---------- fixtures: the program each parity theorem compiles, and its
   oracle file in python-o1-no-asm-opt ---------- *)
val fixtures = [
  ("EMPTY", "empty.hex"),
  ("account_items_program", "account_items.hex"),
  ("add_arg_program", "add_arg.hex"),
  ("assert_bare_program", "assert_bare.hex"),
  ("assert_reason_program", "assert_reason.hex"),
  ("deploy_storage_program", "deploy_storage.hex"),
  ("ec_builtins_program", "ec_builtins.hex"),
  ("env_block_program", "env_block.hex"),
  ("env_message_core_program", "env_message_core.hex"),
  ("env_tx_chain_program", "env_tx_chain.hex"),
  ("event_log_program", "event_log.hex"),
  ("for_accum_program", "for_accum.hex"),
  ("for_break_program", "for_break.hex"),
  ("for_continue_program", "for_continue.hex"),
  ("for_pass_program", "for_pass.hex"),
  ("function_modes_program", "function_modes.hex"),
  ("hash_builtins_program", "hash_builtins.hex"),
  ("hashmap_read_program", "hashmap_read.hex"),
  ("hashmap_write_program", "hashmap_write.hex"),
  ("if_bool_program", "if_bool.hex"),
  ("if_join_program", "if_join.hex"),
  ("indexed_event_log_program", "indexed_event_log.hex"),
  ("internal_call_arg_program", "internal_call_arg.hex"),
  ("internal_call_program", "internal_call.hex"),
  ("local_uint_program", "local_uint.hex"),
  ("loops_program", "loops.hex"),
  ("mixed_event_log_program", "mixed_event_log.hex"),
  ("noop_program", "noop.hex"),
  ("raise_bare_program", "raise_bare.hex"),
  ("raise_reason_program", "raise_reason.hex"),
  ("return_arg_program", "return_arg.hex"),
  ("return_uint_program", "return_uint.hex"),
  ("scalar_arith_decimal_div_program", "scalar_arith_decimal_div.hex"),
  ("scalar_arith_decimal_mul_program", "scalar_arith_decimal_mul.hex"),
  ("scalar_arith_decimal_program", "scalar_arith_decimal.hex"),
  ("scalar_arith_decimal_sub_program", "scalar_arith_decimal_sub.hex"),
  ("scalar_arith_int_program", "scalar_arith_int.hex"),
  ("scalar_arith_pow_base_program", "scalar_arith_pow_base.hex"),
  ("scalar_arith_pow_program", "scalar_arith_pow.hex"),
  ("scalar_arith_uint_program", "scalar_arith_uint.hex"),
  ("scalar_arith_unsafe_int_program", "scalar_arith_unsafe_int.hex"),
  ("scalar_arith_unsafe_uint_program", "scalar_arith_unsafe_uint.hex"),
  ("scalar_bits_program", "scalar_bits.hex"),
  ("scalar_compare_eq_program", "scalar_compare_eq.hex"),
  ("scalar_compare_order_int_program", "scalar_compare_order_int.hex"),
  ("scalar_compare_order_uint_program", "scalar_compare_order_uint.hex"),
  ("scalar_convert_address_program", "scalar_convert_address.hex"),
  ("scalar_convert_bytes32_to_address_program", "scalar_convert_bytes32_to_address.hex"),
  ("scalar_convert_bytes32_to_bytes4_program", "scalar_convert_bytes32_to_bytes4.hex"),
  ("scalar_convert_bytes32_to_decimal_program", "scalar_convert_bytes32_to_decimal.hex"),
  ("scalar_convert_bytes_dynamic_program", "scalar_convert_bytes_dynamic.hex"),
  ("scalar_convert_bytes_fixed_program", "scalar_convert_bytes_fixed.hex"),
  ("scalar_convert_decimal_program", "scalar_convert_decimal.hex"),
  ("scalar_convert_int_to_decimal_program", "scalar_convert_int_to_decimal.hex"),
  ("scalar_convert_integer_program", "scalar_convert_integer.hex"),
  ("scalar_convert_uint_to_bytes32_program", "scalar_convert_uint_to_bytes32.hex"),
  ("scalar_decimal_bounds_program", "scalar_decimal_bounds.hex"),
  ("scalar_decimal_max_program", "scalar_decimal_max.hex"),
  ("scalar_decimal_min_program", "scalar_decimal_min.hex"),
  ("scalar_empty_program", "scalar_empty.hex"),
  ("scalar_integer_bounds_program", "scalar_integer_bounds.hex"),
  ("scalar_integer_max_int256_program", "scalar_integer_max_int256.hex"),
  ("scalar_integer_min_int256_program", "scalar_integer_min_int256.hex"),
  ("scalar_integer_min_uint8_program", "scalar_integer_min_uint8.hex"),
  ("scalar_literal_decimal_program", "scalar_literal_decimal.hex"),
  ("scalar_literals_bool_program", "scalar_literals_bool.hex"),
  ("scalar_literals_bytes_program", "scalar_literals_bytes.hex"),
  ("scalar_literals_int_small_program", "scalar_literals_int_small.hex"),
  ("scalar_literals_int_wide_program", "scalar_literals_int_wide.hex"),
  ("scalar_minmax_int_program", "scalar_minmax_int.hex"),
  ("scalar_minmax_uint_program", "scalar_minmax_uint.hex"),
  ("scalar_modular_program", "scalar_modular.hex"),
  ("scalar_shifts_program", "scalar_shifts.hex"),
  ("scalar_unary_program", "scalar_unary.hex"),
  ("scalar_wei_large_program", "scalar_wei_large.hex"),
  ("scalar_wei_small_program", "scalar_wei_small.hex"),
  ("scalar_widths_int_high_program", "scalar_widths_int_high.hex"),
  ("scalar_widths_int_low_program", "scalar_widths_int_low.hex"),
  ("scalar_widths_uint_high_program", "scalar_widths_uint_high.hex"),
  ("scalar_widths_uint_low_program", "scalar_widths_uint_low.hex"),
  ("storage_array_program", "storage_array.hex"),
  ("storage_dynarray_program", "storage_dynarray.hex"),
  ("storage_mapping_program", "storage_mapping.hex"),
  ("storage_read_program", "storage_read.hex"),
  ("storage_scalar_loop_program", "storage_scalar_loop.hex"),
  ("storage_struct_program", "storage_struct.hex"),
  ("storage_write_program", "storage_write.hex"),
  ("task090_abi_dynamic_program", "abi_dynamic.hex"),
  ("task090_abi_static_program", "abi_static.hex"),
  ("task090_external_arrays_program", "external_arrays.hex"),
  ("task090_external_dynamic_program", "external_dynamic.hex"),
  ("task090_external_scalars_program", "external_scalars.hex"),
  ("task090_external_struct_program", "external_struct.hex"),
  ("task090_interface_calls_program", "interface_calls.hex"),
  ("task090_internal_bytes_call_program", "internal_bytes_call.hex"),
  ("task090_internal_struct_call_program", "internal_struct_call.hex"),
  ("task090_internal_tuple_call_program", "internal_tuple_call.hex"),
  ("task090_mixed_event_types_program", "mixed_event_types.hex"),
  ("task090_send_value_program", "send_value.hex"),
  ("transient_scalar_program", "transient_scalar.hex"),
  ("two_external_program", "two_external.hex")];
fun program_term "EMPTY" = ``[] : toplevel list``
  | program_term p = Term [QUOTE p];

(* ---------- generic helpers ---------- *)
type key = string * string;  (* (Thy, Name) *)
val key_cmp = Lib.pair_compare (String.compare, String.compare);
fun key c = let val {Thy, Name, ...} = dest_thy_const c in (Thy, Name) end;
fun show (t, n) = t ^ "$" ^ n;
(* The definition being normalised, named in the Stuck messages of its code. *)
val eq_owner = ref "";
fun generic (t, n) = prim_mk_const {Thy = t, Name = n};
fun sanitize s = String.translate (fn c =>
  if Char.isAlphaNum c orelse c = #"_" then String.str c else "_") s;

(* Tarjan: dependencies before dependants, mutually recursive nodes grouped. *)
fun sccs (n : int) (edges : int -> int list) = let
  val indices = Array.array (n, ~1)
  val lowlinks = Array.array (n, ~1)
  val on_stack = Array.array (n, false)
  val next_index = ref 0
  val stack = ref ([] : int list)
  val groups = ref ([] : int list list)
  fun visit v = let
    val index = !next_index
    val () = next_index := index + 1
    val () = Array.update (indices, v, index)
    val () = Array.update (lowlinks, v, index)
    val () = Array.update (on_stack, v, true)
    val () = stack := v :: !stack
    fun edge w =
      if Array.sub (indices, w) = ~1 then
        (visit w;
         Array.update (lowlinks, v,
           Int.min (Array.sub (lowlinks, v), Array.sub (lowlinks, w))))
      else if Array.sub (on_stack, w) then
        Array.update (lowlinks, v,
          Int.min (Array.sub (lowlinks, v), Array.sub (indices, w)))
      else ()
    val () = List.app edge (edges v)
    fun pop acc = case !stack of
        [] => raise Fail "sccs: empty stack"
      | w :: rest =>
          (stack := rest; Array.update (on_stack, w, false);
           if w = v then w :: acc else pop (w :: acc))
  in
    if Array.sub (lowlinks, v) = index then groups := pop [] :: !groups else ()
  end
  val () = List.app (fn i => if Array.sub (indices, i) = ~1 then visit i else ())
                    (List.tabulate (n, fn i => i))
in rev (!groups) end;

(* ---------- compset view ---------- *)
val rules_tab = List.foldl (fn (((n, t), trs), d) =>
    Redblackmap.insert (d, (t, n), trs))
  (Redblackmap.mkDict key_cmp) (computeLib.listItems (computeLib.the_compset ()));
fun rrules k = case Redblackmap.peek (rules_tab, k) of
    NONE => []
  | SOME trs => List.concat (map (fn clauses.RRules ths => ths | _ => []) trs);

(* ---------- natives ---------- *)
(* Constants implemented by compilerNativeRuntime.  Each maps to hn_<name>.
   Width-dependent results (result_width) get one instance per concrete
   result width, hn_<name>__<width>. *)
val native_names = [
  ("arithmetic", ["+", "-", "*", "DIV", "MOD", "EXP", "<=", ">", ">=", "MAX", "MIN",
                  "ODD", "EVEN", "DIV2", "FUNPOW", "NUMERAL", "BIT1", "BIT2", "ZERO"]),
  ("prim_rec", ["<", "PRE"]), ("num", ["SUC"]),
  ("words", ["n2w_itself", "w2n", "w2w_itself", "sw2sw_itself", "word_concat_itself",
             "word_extract_itself", "word_eq", "word_add", "word_sub", "word_mul",
             "word_2comp", "word_1comp", "word_and", "word_or", "word_xor", "word_lsl",
             "word_lsr", "word_asr", "word_ror", "word_rol", "word_msb", "word_lsb",
             "word_lo", "word_ls", "word_hi", "word_hs", "word_lt", "word_le", "word_gt",
             "word_ge", "word_div", "word_mod", "word_sdiv", "word_bits", "word_slice",
             "word_bit", "word_index", "dimword", "INT_MIN", "INT_MAX", "UINT_MAX",
             "concat_word_list", "word_log2", "w2i", "n2w", "w2w", "sw2sw"]),
  ("integer", ["int_of_num", "int_neg", "Num", "int_lt", "int_le", "int_gt", "int_ge",
               "int_add", "int_sub", "int_mul", "int_div", "int_mod", "int_quot",
               "int_rem", "ABS", "int_exp"]),
  ("integer_word", ["i2w", "w2i"]),
  ("string", ["CHR", "ORD"]),
  ("finite_map", ["FEMPTY", "FUPDATE", "FLOOKUP", "FAPPLY", "FDOM", "FUNION", "DRESTRICT",
                  "fdomsub", "FEVERY", "FUPDATE_LIST", "FRANGE", "o_f"]),
  ("alist", ["fmap_to_alist"]),
  ("pred_set", ["EMPTY", "INSERT", "DIFF", "DELETE", "COMPL", "UNION", "INTER", "SUBSET"]),
  ("bool", ["IN", "!", "?", "?!", "@"]),
  ("min", ["==>", "@"]),
  ("list", ["LIST_TO_SET", "SET_TO_LIST", "GENLIST", "SNOC", "EL", "LENGTH"]),
  ("relation", ["RTC"]),
  ("toto", ["apto"]),
  ("fcp", ["dimindex"]),
  ("byte", ["byte_index", "get_byte", "set_byte", "word_of_bytes", "word_of_bytes_be",
            "word_to_bytes", "word_to_bytes_aux"]),
  ("bitstring", ["v2w", "w2v"])];
val result_width_names =
  [("words", "concat_word_list"), ("integer_word", "i2w"), ("byte", "word_of_bytes_be"),
   ("bitstring", "v2w")];
fun is_native ((kt, kn) : key) = List.exists (fn (t, ns) => t = kt andalso mem kn ns) native_names;
fun is_result_width k = mem k result_width_names;
val symbolic_names = [("+", "add"), ("-", "sub"), ("*", "mul"), ("<", "lt"), ("<=", "le"),
  (">", "gt"), (">=", "ge"), ("!", "forall"), ("?", "exists"), ("?!", "exists1"),
  ("@", "select"), ("==>", "imp")];
fun native_ml_name (_, n) = "hn_" ^
  (case List.find (fn (s, _) => s = n) symbolic_names of SOME (_, m) => m | NONE => sanitize n);

(* ---------- definitional rule selection ---------- *)
(* TypeBase.is_case recognises applied case terms, not the bare constant. *)
fun is_case_const c =
  same_const c (TypeBase.case_const_of (fst (dom_rng (type_of c)))) handle _ => false;
fun is_constructor c = TypeBase.is_constructor c orelse
  (case total dest_thy_const c of
     SOME {Thy = "pair", Name = ",", ...} => true
   | _ => false);
fun is_lit tm = numSyntax.is_numeral tm orelse
  can Literal.relaxed_dest_string_lit tm orelse can stringSyntax.fromHOLchar tm;
fun pattern_ok tm =
  is_var tm orelse is_lit tm orelse
  (let val (f, args) = strip_comb tm
   in is_const f andalso is_constructor f andalso List.all pattern_ok args end);
fun linear args = let val vs = List.concat (map free_vars args)
  in length vs = length (Lib.op_mk_set aconv vs) end;
fun definitional c th =
  let val body = snd (strip_forall (concl th)) in
    if is_imp body orelse not (is_eq body) then false else
    let val (f, args) = strip_comb (lhs body) in
      is_const f andalso same_const f c andalso List.all pattern_ok args andalso linear args
    end
  end;
(* An equation with no arguments defines the constant outright; extra compset
   rules for it (e.g. num_to_dec_string's specialisation) are dropped. *)
fun about c th = let val body = snd (strip_forall (concl th))
                     val body = if is_imp body then snd (dest_imp body) else body
  in is_eq body andalso same_const (fst (strip_comb (lhs body))) c end handle HOL_ERR _ => false;
(* When the compset states some equations with numeral patterns (TAKE's
   NUMERAL (BIT1 n)) or side conditions, the definitional ones alone would
   define a partial function; use the constant's definition instead. *)
val replaced : (key * string) list ref = ref [];
fun stored_def k = let
  val c = generic k
  val eqs = List.concat (map (fn (_, th) => List.filter (fn eq => about c (ASSUME eq))
              (map (snd o strip_forall) (strip_conj (concl th)))) (DB.definitions (#1 k)))
  fun recursion_combinator tm = is_const tm andalso
    mem (key tm) [("relation", "WFREC"), ("relation", "WF"), ("min", "@")]
in if not (null eqs) andalso List.all (fn eq => definitional c (ASSUME eq)) eqs andalso
      not (List.exists (can (find_term recursion_combinator)) eqs) then SOME eqs else NONE end;
(* Computable restatements, proved here, of definitions whose quantifiers EVAL
   leaves unevaluated in a term it later discards; native code is strict, so
   it needs them decided. *)
val code_equations = map (fn th => (key (fst (strip_comb (lhs (snd (strip_forall (concl th)))))), th)) [
  prove (``lower_dload_invalidates_layout fn <=>
           EXISTS (\bb. EXISTS (\inst. inst.inst_opcode = DLOAD /\
                     LENGTH inst.inst_operands = 1 /\ LENGTH inst.inst_outputs = 1)
                   bb.bb_instructions) fn.fn_blocks``,
    rw[lowerDloadDefsTheory.lower_dload_invalidates_layout_def, listTheory.EXISTS_MEM,
       listTheory.LENGTH_EQ_NUM_compute] >> metis_tac[])];
(* Proved rewrites applied to every right-hand side: they turn set
   inclusions over finite collections and bounded quantifiers into the list
   and finite-map functions that native code computes. *)
val code_rewrites = [
  prove (``FDOM m SUBSET s <=> FEVERY (\kv. FST kv IN s) m``,
    rw[finite_mapTheory.FEVERY_DEF, pred_setTheory.SUBSET_DEF]),
  prove (``set l SUBSET s <=> EVERY (\x. x IN s) l``,
    rw[pred_setTheory.SUBSET_DEF, listTheory.EVERY_MEM]),
  GSYM listTheory.EXISTS_MEM, GSYM listTheory.EVERY_MEM];
fun rewrite_rhs eq = let val r = rhs eq
  in mk_eq (lhs eq, rhs (concl (QCONV (Ho_Rewrite.PURE_REWRITE_CONV code_rewrites) r))) end;
fun def_rules k = map rewrite_rhs (case Lib.assoc1 k code_equations of
    SOME (_, th) => [snd (strip_forall (concl th))]
  | NONE => def_rules0 k)
and def_rules0 k = let
  val c = generic k
  val rules = List.filter (about c) (rrules k)
  val eqs = Lib.op_mk_set aconv
    (map (snd o strip_forall o concl) (List.filter (definitional c) rules))
  val eqs = if List.all (definitional c) rules then eqs
            else case stored_def k of
                   SOME d => (replaced := (k, "definition") :: !replaced; d)
                 | NONE => (replaced := (k, "PARTIAL") :: !replaced; eqs)
  (* Several catch-all equations (a definition plus a computable restatement,
     like lower_dload_invalidates_layout's): ML would only ever use the first,
     so keep one, preferring one without quantifiers. *)
  fun catch_all eq = List.all is_var (snd (strip_comb (lhs eq)))
  fun quantified eq = can (find_term (fn t => is_const t andalso
    mem (key t) [("bool", "!"), ("bool", "?"), ("bool", "?!"), ("min", "@")])) (rhs eq)
  val eqs = case List.filter catch_all eqs of
      _ :: _ :: _ => let val alls = List.filter catch_all eqs
                         val best = case List.find (not o quantified) alls of
                                      SOME eq => eq | NONE => hd alls
                     in List.filter (fn eq => not (catch_all eq) orelse aconv eq best) eqs end
    | _ => eqs
in case List.find (is_const o lhs) eqs of SOME eq => [eq] | NONE => eqs end;

(* Record field updates: derived from the accessor equations' constructor. *)
fun record_info k = let
  val c = generic k
  val (_, rty) = dom_rng (snd (dom_rng (type_of c)))
in
  case TypeBase.fields_of rty of
    [] => NONE
  | fields => let
      val (_, {ty = fty, ...}) = valOf (List.find (fn (_, {fupd, ...}) =>
          same_const fupd c) fields) handle Option => raise Fail "record_info"
      val idx = Lib.index (fn (_, {fupd, ...}) => same_const fupd c) fields
    in SOME (rty, fields, idx) end
end handle HOL_ERR _ => NONE;
fun fupd_rules k = case record_info k of
    NONE => []
  | SOME (rty, fields, idx) => let
      val cons = case TypeBase.constructors_of rty of [x] => x | _ => raise Fail "fupd"
      val (argtys, _) = strip_fun (type_of cons)
      val vars = mapi (fn i => fn ty => mk_var ("r" ^ Int.toString i, ty)) argtys
      val c = generic k
      val f = mk_var ("f", fst (dom_rng (type_of c)))
      val cons = Term.inst (match_type (snd (strip_fun (type_of cons))) rty) cons
      val c = Term.inst (match_type (snd (dom_rng (snd (dom_rng (type_of c))))) rty) c
      val pat = list_mk_comb (cons, vars)
      val newv = mapi (fn i => fn v => if i = idx then mk_comb (f, v) else v) vars
    in [mk_eq (list_mk_comb (c, [f, pat]), list_mk_comb (cons, newv))] end
    handle HOL_ERR _ => [];

(* ML names: c<i>_<name> for emitted constants, K<i>_<name> for constructors. *)
val name_tab : (key, string) Redblackmap.dict ref = ref (Redblackmap.mkDict key_cmp);
val name_count = ref 0;
fun ml_name prefix k = case Redblackmap.peek (!name_tab, k) of
    SOME s => s
  | NONE => let val s = prefix ^ Int.toString (!name_count) ^ "_" ^ sanitize (#2 k)
            in name_count := !name_count + 1;
               name_tab := Redblackmap.insert (!name_tab, k, s); s end;

(* toto values: equations apto C x y = rhs define C as a comparison function,
   which is how the runtime represents a toto. *)
fun toto_rules k = let
  val c = generic k
  val apto_rules = rrules (key ``toto$apto``)
  fun for_c eq = let val (l, r) = dest_eq (snd (strip_forall (concl eq)))
                     val (_, args) = strip_comb l
                 in case args of
                      [t, x, y] => if is_const t andalso same_const t c
                                   then let val f = list_mk_abs ([x, y], r)
                                        in SOME (mk_eq (mk_var ("^" ^ ml_name "c" k, type_of f), f)) end
                                   else NONE
                    | _ => NONE end
in List.mapPartial for_c apto_rules end;

(* ---------- closure ---------- *)
val seen : (key, unit) Redblackmap.dict ref = ref (Redblackmap.mkDict key_cmp);
val defs : (key * term list) list ref = ref [];
val missing : (key * string) list ref = ref [];
val natives_used : (key, unit) Redblackmap.dict ref = ref (Redblackmap.mkDict key_cmp);
val users : (key, key list) Redblackmap.dict ref = ref (Redblackmap.mkDict key_cmp);
fun note_user k u = users := Redblackmap.insert (!users, k,
  u :: (case Redblackmap.peek (!users, k) of NONE => [] | SOME l => l));
fun consts_of tm = find_terms is_const tm;
fun visit u c =
  let val k = key c
      val () = note_user k u in
    if isSome (Redblackmap.peek (!seen, k)) then () else
    (seen := Redblackmap.insert (!seen, k, ());
     if is_native k then natives_used := Redblackmap.insert (!natives_used, k, ())
     else if is_constructor c orelse is_case_const c then ()
     else if mem k [("bool", "COND"), ("bool", "LET"), ("min", "="), ("bool", "/\\"),
                    ("bool", "\\/"), ("bool", "~"), ("bool", "T"), ("bool", "F"),
                    ("bool", "ARB"), ("bool", "literal_case"), ("bool", "the_value")]
     then ()
     else
       let val eqs = case def_rules k of
                       [] => (case fupd_rules k of [] => toto_rules k | l => l)
                     | l => l
       in
         if null eqs then
           missing := (k, type_to_string (type_of (generic k))) :: !missing
         else (defs := (k, eqs) :: !defs;
               List.app (List.app (visit k) o consts_of o rhs) eqs)
       end)
  end;
val root_terms = ``compile_vyper (K SOME) (o1_policy all_capabilities)`` ::
  map (program_term o #1) fixtures;
val () = List.app (List.app (visit ("", "ROOT")) o consts_of) root_terms;
fun users_of k = let val us = Lib.mk_set (Redblackmap.find (!users, k)) handle NotFound => []
  in String.concatWith " " (map show (List.take (us, Int.min (4, length us)))) end;
val () = pr ("defined constants: " ^ Int.toString (length (!defs)) ^ ", rules " ^
  Int.toString (List.foldl (fn ((_, l), n) => n + length l) 0 (!defs)) ^ "\n");
val () = pr ("natives used: " ^ String.concatWith " " (map (show o #1)
  (Redblackmap.listItems (!natives_used))) ^ "\n");
val () = pr ("missing (" ^ Int.toString (length (!missing)) ^ "):\n" ^
  String.concat (map (fn (k, s) => "  " ^ show k ^ " : " ^ s ^ "\n    used by " ^
    users_of k ^ "\n") (rev (!missing))));
val () = if null (!missing) then () else raise Fail "constants without equations";
val () = pr ("rules replaced (" ^ Int.toString (length (!replaced)) ^ "): " ^
  String.concatWith " " (map (fn (k, s) => show k ^ "=" ^ s) (rev (!replaced))) ^ "\n");

(* ---------- equation normalisation ---------- *)
val var_count = ref 0;
fun fresh_var ty = (var_count := !var_count + 1;
                    mk_var ("hv" ^ Int.toString (!var_count), ty));
fun is_raw_var v = is_var v andalso String.isPrefix "^" (fst (dest_var v));

(* Fully apply constructors, case constants and equality, so EmitML prints
   them as ML constructor applications, case expressions and infix =. *)
fun needed_arity c =
  if is_constructor c then
    (if same_const c pairSyntax.comma_tm then 2 else length (fst (strip_fun (type_of c))))
  else if is_case_const c then
    1 + length (TypeBase.constructors_of (fst (dom_rng (type_of c))))
  else if same_const c boolSyntax.equality then 2
  else 0;
fun eta_full tm =
  if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, eta_full b) end
  else let
    val (h, args) = strip_comb tm
    val args = map eta_full args
    val h = if is_abs h then eta_full h else h
  in
    if is_const h andalso length args < needed_arity h then let
      val (argtys, _) = strip_fun (type_of (list_mk_comb (h, args)))
      val extra = List.take (argtys, needed_arity h - length args)
      val vs = map fresh_var extra
    in list_mk_abs (vs, list_mk_comb (h, args @ vs)) end
    else list_mk_comb (h, args)
  end;

fun rename_bound tm =
  if is_abs tm then let val (v, b) = dest_abs tm
                        val nv = fresh_var (type_of v)
                    in mk_abs (nv, rename_bound (subst [v |-> nv] b)) end
  else if is_comb tm then mk_comb (rename_bound (rator tm), rename_bound (rand tm))
  else tm;
fun rename_vars eq = let
  val fvs = free_vars eq
  val theta = map (fn v => v |-> fresh_var (type_of v)) (List.filter (not o is_raw_var) fvs)
in rename_bound (subst theta eq) end;

fun drop_literal_case tm =
  if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, drop_literal_case b) end
  else if is_comb tm then let
    val (h, args) = strip_comb tm
  in
    if is_const h andalso same_const h ``literal_case`` andalso length args >= 2 then
      drop_literal_case (list_mk_comb (beta_conv (mk_comb (hd args, el 2 args))
                                       handle HOL_ERR _ => mk_comb (hd args, el 2 args),
                                       List.drop (args, 2)))
    else mk_comb (drop_literal_case (rator tm), drop_literal_case (rand tm))
  end
  else tm;

(* Uniform clause arity: peel leading (paired) abstractions of the right-hand
   side, or apply it to fresh variables, until every clause has as many
   arguments as the longest. *)
fun lam_depth tm = if pairSyntax.is_pabs tm then 1 + lam_depth (snd (pairSyntax.dest_pabs tm)) else 0;
fun uniform_arity eqs = let
  val arity = List.foldl Int.max 0 (map (fn eq => length (snd (strip_comb (lhs eq))) +
                                          (if length eqs = 1 then lam_depth (rhs eq) else 0)) eqs)
  fun pad eq = let
    val (l, r) = dest_eq eq
    val n = length (snd (strip_comb l))
  in
    if n >= arity then eq
    else if pairSyntax.is_pabs r then let
      val (vs, b) = pairSyntax.dest_pabs r
    in pad (mk_eq (mk_comb (l, vs), b)) end
    else let val v = fresh_var (fst (dom_rng (type_of r)))
         in pad (mk_eq (mk_comb (l, v), mk_comb (r, v))) end
  end
in map pad eqs end;

(* ---------- literals ---------- *)
val lit_decls : (string * string) list ref = ref [];  (* (ml text, var name) *)
fun hoist prefix text = case List.find (fn (t, _) => t = text) (!lit_decls) of
    SOME (_, v) => v
  | NONE => let val v = prefix ^ Int.toString (length (!lit_decls))
            in lit_decls := (text, v) :: !lit_decls; v end;
fun raw ty s = mk_var ("^" ^ s, ty);
fun num_text n = Arbnum.toString n;
(* Leading space: EmitML prints h::t without spaces, and ::# would lex as one
   symbolic identifier. *)
fun char_text c = " #\"" ^ String.toString (String.str c) ^ "\"";
fun concrete_width ty =
  SOME (Arbnum.toInt (fcpSyntax.dest_numeric_type (wordsSyntax.dest_word_type ty)))
  handle HOL_ERR _ => NONE;
fun is_char_lit tm = can stringSyntax.fromHOLchar tm;
fun is_string_lit tm = can Literal.relaxed_dest_string_lit tm andalso
                       type_of tm = stringSyntax.string_ty;
fun lits side tm =
  if numSyntax.is_numeral tm then
    let val n = num_text (numSyntax.dest_numeral tm) in
      if side = EmitML.LEFT then raw (type_of tm) ("(" ^ n ^ ":IntInf.int)")
      else raw (type_of tm) (hoist "numlit_" ("(" ^ n ^ " : IntInf.int)")) end
  else if is_string_lit tm then tm
  else if is_char_lit tm then raw (type_of tm) (char_text (stringSyntax.fromHOLchar tm))
  else if side = EmitML.RIGHT andalso wordsSyntax.is_n2w tm andalso
          numSyntax.is_numeral (rand tm) andalso isSome (concrete_width (type_of tm)) then
    raw (type_of tm) (hoist "wordlit_" ("hn_n2w " ^ Int.toString (valOf (concrete_width (type_of tm))) ^
          " (" ^ num_text (numSyntax.dest_numeral (rand tm)) ^ " : IntInf.int)"))
  else if is_const tm andalso same_const tm ``the_value`` then raw (type_of tm) "()"
  else if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, lits side b) end
  else if is_comb tm then mk_comb (lits side (rator tm), lits side (rand tm))
  else tm;
fun literal_eq eq = let val (l, r) = dest_eq eq
                        val (f, args) = strip_comb l
                    in mk_eq (list_mk_comb (f, map (lits EmitML.LEFT) args), lits EmitML.RIGHT r) end;

(* Native nums have no SUC constructor: a clause f (SUC n) = r becomes
   f m = if m = 0 then ARB else let n = m - 1 in r, placed after the other
   clauses so that literal patterns still take priority. *)
fun suc_pattern eq = let
  val (l, r) = dest_eq eq
  val (f, args) = strip_comb l
  fun arg (a, (acc, conds, binds)) =
    if numSyntax.is_suc a then let
      val n = numSyntax.dest_suc a
      val () = if is_var n then () else raise Fail "nested SUC pattern"
      val m = fresh_var numSyntax.num
    in (m :: acc, mk_eq (m, numSyntax.zero_tm) :: conds,
        (n, numSyntax.mk_minus (m, numSyntax.term_of_int 1)) :: binds) end
    else (if can (find_term numSyntax.is_suc) a then raise Fail "SUC inside a pattern" else ();
          (a :: acc, conds, binds))
  val (args', conds, binds) = List.foldl arg ([], [], []) args
in
  if null conds then (false, eq)
  else (true, mk_eq (list_mk_comb (f, rev args'),
          mk_cond (list_mk_disj conds, raw (type_of r) ("(hn_nomatch " ^ Lib.mlquote (!eq_owner) ^ ")"),
                   List.foldl (fn ((n, e), b) => mk_let (mk_abs (n, b), e)) r binds)))
end;
fun suc_patterns eqs = let val es = map suc_pattern eqs
  in map #2 (List.filter (not o #1) es @ List.filter #1 es) end;

(* Sets and functions have no ML equality, nor do datatypes that contain
   them; HOL equality at such a type becomes hn_badeq, which raises Stuck when
   run.  Equality between finite maps is hn_fmap_eq, which is extensional. *)
fun noneq_ty seen ty =
  not (is_vartype ty) andalso
  let val {Thy, Tyop, Args} = dest_thy_type ty
      val k = (Thy, Tyop)
  in case k of
       ("min", "fun") => true
     | ("toto", "toto") => true
     | ("fcp", "cart") => false
     | _ => List.exists (noneq_ty seen) Args orelse
            (not (mem k seen) andalso
             List.exists (fn c => List.exists (noneq_ty (k :: seen)) (fst (strip_fun (type_of c))))
               (TypeBase.constructors_of (mk_thy_type {Thy = Thy, Tyop = Tyop,
                  Args = map (K alpha) Args}) handle HOL_ERR _ => []))
  end;
(* Quantifiers raise Stuck when run; they carry the definition they occur in. *)
val quantifiers = [("bool", "!"), ("bool", "?"), ("bool", "?!"), ("min", "@")];
fun badeq ty = raw ty ("(hn_badeq " ^ Lib.mlquote (!eq_owner) ^ ")");
fun is_eq_fmap ty = can finite_mapSyntax.dest_fmap_ty ty andalso
  let val (a, b) = finite_mapSyntax.dest_fmap_ty ty in
    not (noneq_ty [] a) andalso not (noneq_ty [] b) end;
(* ARB: a placeholder that EVAL carries along unevaluated (an absent
   constructor's environment, say).  Native code needs a value, so ARB becomes
   a default value of its type: a nullary or non-recursive constructor applied
   to defaults.  A function-typed ARB raises Stuck when applied. *)
fun default_text seen ty =
  if is_vartype ty then raise mk_HOL_ERR "native" "default_text" "type variable" else
  let val {Thy, Tyop, Args} = dest_thy_type ty
      fun d t = default_text seen t
  in case (Thy, Tyop) of
      ("min", "bool") => "false"
    | ("min", "fun") => "(fn _ => hn_arb \"function\")"
    | ("num", "num") => "(0 : IntInf.int)"
    | ("integer", "int") => "(0 : IntInf.int)"
    | ("string", "char") => "#\"\\000\""
    | ("list", "list") => if hd Args = stringSyntax.char_ty then "\"\"" else "[]"
    | ("option", "option") => "NONE"
    | ("pair", "prod") => "(" ^ d (hd Args) ^ ", " ^ d (el 2 Args) ^ ")"
    | ("one", "one") => "()"
    | ("bool", "itself") => "()"
    | ("finite_map", "fmap") => "hn_FEMPTY"
    | ("fcp", "cart") => (case concrete_width ty of
                            SOME w => "(W (" ^ Int.toString w ^ ", 0))"
                          | NONE => raise mk_HOL_ERR "native" "default_text" "width")
    | k => if mem k seen then raise mk_HOL_ERR "native" "default_text" "recursive" else let
        val cs = TypeBase.constructors_of ty
        fun try c = let
          val c = Term.inst (match_type (snd (strip_fun (type_of c))) ty) c
          val args = fst (strip_fun (type_of c))
          val name = ml_name "K" (key c)
        in if null args then name
           else name ^ "(" ^ String.concatWith ", " (map (default_text (k :: seen)) args) ^ ")" end
        fun first [] = raise mk_HOL_ERR "native" "default_text" "no constructor"
          | first (c :: rest) = (try c handle HOL_ERR _ => first rest)
      in "(" ^ first cs ^ ")" end
  end;
fun guard_eq tm =
  if is_eq tm andalso is_eq_fmap (type_of (lhs tm)) then let val ty = type_of (lhs tm)
    in list_mk_comb (raw (ty --> ty --> bool) "hn_fmap_eq", [guard_eq (lhs tm), guard_eq (rhs tm)]) end
  else if is_eq tm andalso noneq_ty [] (type_of (lhs tm)) then let val ty = type_of (lhs tm)
    in list_mk_comb (badeq (ty --> ty --> bool), [guard_eq (lhs tm), guard_eq (rhs tm)]) end
  else if listSyntax.is_mem tm andalso noneq_ty [] (type_of (fst (listSyntax.dest_mem tm))) then
    let val (x, l) = listSyntax.dest_mem tm
    in list_mk_comb (badeq (type_of x --> type_of l --> bool), [guard_eq x, guard_eq l]) end
  else if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, guard_eq b) end
  else if is_comb tm then mk_comb (guard_eq (rator tm), guard_eq (rand tm))
  else if is_const tm andalso key tm = ("bool", "ARB") then
    raw (type_of tm) (default_text [] (type_of tm)
                      handle HOL_ERR _ => "(hn_arb " ^ Lib.mlquote (!eq_owner) ^ ")")
  else if is_const tm andalso mem (key tm) quantifiers then
    raw (type_of tm) ("(" ^ native_ml_name (key tm) ^ " " ^ Lib.mlquote (!eq_owner) ^ ")")
  else tm;
fun guard_eq_rhs eq = mk_eq (lhs eq, guard_eq (rhs eq));

(* EmitML parenthesises neither a case expression nor a fn that ends a case
   arm or an if branch, so a following arm would be parsed as part of it.
   Wrapping them in the identity hn_paren makes EmitML print parentheses. *)
fun paren tm = mk_comb (raw (type_of tm --> type_of tm) "hn_paren", tm);
fun parens tm =
  if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, parens b) end
  else if is_comb tm then let
    val (h, args) = strip_comb tm
  in
    if is_const h andalso is_case_const h then let
      val n = needed_arity h
      val (args0, extra) = (List.take (args, n), List.drop (args, n))
      val dty = type_of (hd args0)
      val arities = map (length o fst o strip_fun o type_of) (TypeBase.constructors_of dty)
      fun arm (k, b) = let
        val (vs, body) = strip_abs b
      in if length vs < k then parens b
         else let val (bvs, rest) = (List.take (vs, k), List.drop (vs, k))
                  val body' = parens (list_mk_abs (rest, body))
              in list_mk_abs (bvs, if is_abs body' then paren body' else body') end
      end
      val c = list_mk_comb (h, parens (hd args0) :: map arm (zip arities (tl args0)))
    in list_mk_comb (paren c, map parens extra) end
    else if is_cond tm then let
      val (c, t, e) = dest_cond tm
      fun br x = let val x' = parens x in if is_abs x' then paren x' else x' end
    in mk_cond (parens c, br t, br e) end
    else list_mk_comb (parens h, map parens args)
  end
  else tm;
fun parens_rhs eq = mk_eq (lhs eq, parens (rhs eq));

(* A record literal <| f1 := v1; ... |> is a chain of field updates on ARB.
   When every field is set, build the constructor application instead. *)
fun fupd_info c = if is_const c then (record_info (key c) handle Fail _ => NONE) else NONE;
fun update_value f =
  case strip_comb f of
    (k, [v]) => if is_const k andalso key k = ("combin", "K") then SOME v else NONE
  | _ => if is_abs f andalso not (free_in (bvar f) (body f)) then SOME (body f) else NONE;
fun record_literals tm =
  if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, record_literals b) end
  else if not (is_comb tm) then tm
  else let
    val (h, args) = strip_comb tm
    val info = if length args = 2 then fupd_info h else NONE
    fun chain t acc =
      case strip_comb t of
        (u, [f, r]) =>
          (case (fupd_info u, update_value f) of
             (SOME (_, _, i), SOME v) =>
               chain r (if isSome (Lib.assoc1 i acc) then acc else (i, v) :: acc)
           | _ => NONE)
      | (a, []) => if is_const a andalso key a = ("bool", "ARB") then SOME acc else NONE
      | _ => NONE
  in
    case (info, chain tm []) of
      (SOME (rty, fields, _), SOME vals) =>
        if length vals = length fields then let
          val cons = hd (TypeBase.constructors_of rty)
          val cons = Term.inst (match_type (snd (strip_fun (type_of cons))) rty) cons
        in list_mk_comb (cons, List.tabulate (length fields, fn i =>
             record_literals (Lib.assoc i vals)))
        end
        else list_mk_comb (record_literals h, map record_literals args)
    | _ => list_mk_comb (record_literals h, map record_literals args)
  end;
fun record_literals_rhs eq = mk_eq (lhs eq, record_literals (rhs eq));

(* Strings: HOL's string is char list, and here it is an ML string, so string
   comparisons are not list traversals.  A string literal prints as one.  CONS
   and a case on a string become hn_scons and hn_scase.  A polymorphic
   constant whose generic type applies list to a type variable that is
   instantiated to char works on lists in ML, so its uses at char convert the
   arguments and result between strings and char lists (explode, implode). *)
val char_ty = stringSyntax.char_ty;
val string_ty = stringSyntax.string_ty;
fun is_string_literal tm = type_of tm = string_ty andalso can Literal.relaxed_dest_string_lit tm;
fun ml_const_name c = let val k = key c in
  if is_native k then
    (if is_result_width k orelse mem k [("words", "n2w"), ("words", "w2w"),
          ("words", "sw2sw"), ("fcp", "dimindex"), ("words", "dimword")]
     then raise Fail ("string coercion of width-indexed native " ^ show k)
     else native_ml_name k)
  else if is_constructor c then ml_name "K" k
  else ml_name "c" k end;
(* Coercions between the instance's ML representation and the generic one:
   NONE when they agree. *)
fun is_char_list theta ty = case total listSyntax.dest_list_type ty of
    SOME a => is_vartype a andalso type_subst theta a = char_ty
  | NONE => false;
fun coercion theta to_generic ty =
  if is_vartype ty then NONE
  else if is_char_list theta ty then
    SOME (if to_generic then "String.explode" else "String.implode")
  else let
    val {Thy, Tyop, Args} = dest_thy_type ty
    val cs = map (coercion theta to_generic) Args
    fun get (SOME s) = s | get NONE = "(fn x => x)"
  in
    if List.all (not o isSome) cs then NONE
    else case ((Thy, Tyop), Args, cs) of
      (("list", "list"), _, [a]) => SOME ("(List.map " ^ get a ^ ")")
    | (("option", "option"), _, [a]) => SOME ("(Option.map " ^ get a ^ ")")
    | (("pair", "prod"), _, [a, b]) =>
        SOME ("(fn (x, y) => (" ^ get a ^ " x, " ^ get b ^ " y))")
    | (("min", "fun"), [a, _], [_, b]) =>
        SOME ("(fn f => fn x => " ^ get b ^ " (f (" ^
              get (coercion theta (not to_generic) a) ^ " x)))")
    | _ => raise Fail ("no string coercion through " ^ type_to_string ty)
  end;
(* List functions at char that have a string counterpart in the runtime. *)
val string_natives = [(("list", "APPEND"), "hn_sAPPEND"), (("list", "LENGTH"), "hn_sLENGTH"),
  (("list", "FLAT"), "hn_sFLAT")];
fun string_const c =
  if is_constructor c orelse is_case_const c then c else let
    val gty = type_of (generic (key c))
    val theta = match_type gty (type_of c)
  in case (Lib.assoc1 (key c) string_natives, theta) of
       (SOME (_, f), [{redex, residue}]) =>
         if residue = char_ty then raw (type_of c) f
         else raise mk_HOL_ERR "native" "string_const" "not at char"
     | _ => raise mk_HOL_ERR "native" "string_const" "no string native"
  end handle HOL_ERR _ => let
    val gty = type_of (generic (key c))
    val theta = match_type gty (type_of c)
  in case coercion theta false gty of
       NONE => c
     | SOME f => raw (type_of c) ("(" ^ f ^ " " ^ ml_const_name c ^ ")")
  end handle HOL_ERR _ => c;
fun is_string_cons c = is_const c andalso same_const c listSyntax.cons_tm andalso
  type_of c = (char_ty --> string_ty --> string_ty);
fun strings tm =
  if is_string_literal tm then tm
  else if is_abs tm then let val (v, b) = dest_abs tm in mk_abs (v, strings b) end
  else if is_comb tm then let
    val (h, args) = strip_comb tm
  in
    if is_string_cons h andalso length args = 2 then
      list_mk_comb (raw (type_of h) "hn_scons", map strings args)
    else if is_const h andalso is_case_const h andalso
            type_of (hd args) = string_ty then let
      val (s, n, f, extra) = case args of
          s :: n :: f :: extra => (s, n, f, extra)
        | _ => raise Fail "string case arity"
      val u = fresh_var oneSyntax.one_ty
      val thunk = mk_abs (u, strings n)
      val rty = type_of n
    in list_mk_comb (raw (string_ty --> type_of thunk --> type_of f --> rty) "hn_scase",
                     [strings s, thunk, strings f] @ map strings extra) end
    else list_mk_comb ((if is_const h then string_const h else strings h), map strings args)
  end
  else if is_const tm then string_const tm
  else tm;
(* Patterns stay as they are: a string literal or "" is an ML pattern, but
   CONS at char is not. *)
fun string_pattern_ok tm =
  is_string_literal tm orelse is_var tm orelse
  (let val (h, args) = strip_comb tm in
     not (is_string_cons h) andalso List.all string_pattern_ok args end);
(* A clause that takes a string apart in its pattern (TFL completes a pattern
   like "code" into one clause per character) has no ML pattern.  Such
   clauses become one final clause that tests them in turn: each test
   matches its clause's pattern with case expressions and returns SOME of the
   right-hand side or NONE.  Every clause is a theorem, so whenever several
   clauses match their right-hand sides agree, and the order of the tests
   does not matter. *)
fun has_string_cons tm =
  not (is_string_literal tm) andalso
  (let val (h, args) = strip_comb tm in
     is_string_cons h orelse List.exists has_string_cons args end);
fun match_pattern (p, x) body = let
  val none = optionSyntax.mk_none (optionSyntax.dest_option (type_of body))
in
  if is_var p then subst [p |-> x] body
  else if is_lit p then mk_cond (mk_eq (x, p), body, none)
  else let
    val (c, ps) = strip_comb p
    val ty = type_of x
    fun arm c' = let
      val c' = Term.inst (match_type (snd (strip_fun (type_of c'))) ty) c'
      val vs = map fresh_var (fst (strip_fun (type_of c')))
    in list_mk_abs (vs, if same_const c c'
                        then List.foldr (fn (pv, b) => match_pattern pv b) body (zip ps vs)
                        else none) end
  in boolSyntax.list_mk_icomb (TypeBase.case_const_of ty,
       x :: map arm (TypeBase.constructors_of ty)) end
end;
fun string_patterns eqs = let
  val (split, plain) = List.partition (List.exists has_string_cons o snd o strip_comb o lhs) eqs
in
  if null split then eqs else let
    val (f, args0) = strip_comb (lhs (hd split))
    val vs = map (fresh_var o type_of) args0
    val rty = type_of (rhs (hd split))
    fun test eq = List.foldr (fn (pv, b) => match_pattern pv b)
      (optionSyntax.mk_some (rhs eq)) (zip (snd (strip_comb (lhs eq))) vs)
    val r = fresh_var rty
    val cascade = List.foldr (fn (eq, rest) =>
        boolSyntax.list_mk_icomb (TypeBase.case_const_of (optionSyntax.mk_option rty),
          [test eq, rest, mk_abs (r, r)]))
      (raw rty ("(hn_nomatch " ^ Lib.mlquote (!eq_owner) ^ ")")) split
  in plain @ [mk_eq (list_mk_comb (f, vs), cascade)] end
end;
val string_pattern_defs : string list ref = ref [];
fun strings_eq eq = let
  val (l, r) = dest_eq eq
  val () = if List.all string_pattern_ok (snd (strip_comb l)) then ()
           else string_pattern_defs := !eq_owner :: !string_pattern_defs
in mk_eq (l, strings r) end;

fun normalise eqs =
  map (literal_eq o parens_rhs o guard_eq_rhs o rename_vars o strings_eq o record_literals_rhs o
       eta_full o drop_literal_case)
    (string_patterns (suc_patterns (uniform_arity eqs)));

val normal_defs = map (fn (k, eqs) => (eq_owner := show k; (k, normalise eqs))) (rev (!defs));
val fixture_terms = map (fn (p, h) =>
    (h, lits EmitML.RIGHT (rename_vars (strings (eta_full ``compile_vyper (K SOME) (o1_policy all_capabilities)
                                                    ^(program_term p)``)))))
  fixtures;
val () = pr ("normalised\n");
val () = if null (!string_pattern_defs) then ()
         else (pr ("string CONS patterns in: " ^
                   String.concatWith " " (Lib.mk_set (!string_pattern_defs)) ^ "\n");
               raise Fail "string CONS patterns")

(* ---------- types ---------- *)
val builtin_tyops = [("min", "bool"), ("min", "fun"), ("num", "num"), ("integer", "int"),
  ("string", "char"), ("list", "list"), ("option", "option"), ("pair", "prod"),
  ("one", "one"), ("fcp", "cart"), ("fcp", "bit0"), ("fcp", "bit1"), ("bool", "itself"),
  ("finite_map", "fmap"), ("toto", "toto")];
fun tyop_key ty = let val {Thy, Tyop, ...} = dest_thy_type ty in (Thy, Tyop) end;
fun tyops ty acc =
  if is_vartype ty then acc
  else let val {Thy, Tyop, Args} = dest_thy_type ty
       in List.foldl (fn (a, acc) => tyops a acc) ((Thy, Tyop) :: acc) Args end;
fun term_tyops tm acc =
  List.foldl (fn (t, acc) => tyops (type_of t) acc) acc
    (find_terms (fn t => is_var t orelse is_const t) tm);

val datatype_tab : (key, int) Redblackmap.dict ref = ref (Redblackmap.mkDict key_cmp);
val datatypes : (key * hol_type * term list) list ref = ref [];  (* reversed *)
fun add_tyop k =
  if mem k builtin_tyops orelse isSome (Redblackmap.peek (!datatype_tab, k)) then ()
  else case TypeBase.read {Thy = #1 k, Tyop = #2 k} of
    NONE => raise Fail ("not a datatype: " ^ show k)
  | SOME info => let
      val ty = TypeBasePure.ty_of info
      val cs = TypeBasePure.constructors_of info
      val () = datatype_tab := Redblackmap.insert (!datatype_tab, k, length (!datatypes))
      val () = datatypes := (k, ty, cs) :: !datatypes
    in List.app (fn c => List.app add_tyop (tyops (type_of c) [])) cs end;
val () = List.app (fn (_, eqs) => List.app (fn eq => List.app add_tyop (term_tyops eq [])) eqs)
                  normal_defs;
val () = List.app (fn (_, tm) => List.app add_tyop (term_tyops tm [])) fixture_terms;
val datatype_vec = Vector.fromList (rev (!datatypes));

fun ml_tyvar ty = "'" ^ sanitize (String.extract (dest_vartype ty, 1, NONE));
fun ml_ty ty =
  if is_vartype ty then ml_tyvar ty else
  let val {Thy, Tyop, Args} = dest_thy_type ty
      fun app1 s = "(" ^ ml_ty (hd Args) ^ ") " ^ s
  in case (Thy, Tyop) of
      ("min", "bool") => "bool"
    | ("min", "fun") => "(" ^ ml_ty (hd Args) ^ " -> " ^ ml_ty (el 2 Args) ^ ")"
    | ("num", "num") => "hn_num"
    | ("integer", "int") => "hn_int"
    | ("string", "char") => "char"
    | ("list", "list") => if hd Args = stringSyntax.char_ty then "string" else app1 "list"
    | ("option", "option") => app1 "option"
    | ("pair", "prod") => "(" ^ ml_ty (hd Args) ^ " * " ^ ml_ty (el 2 Args) ^ ")"
    | ("one", "one") => "unit"
    | ("fcp", "cart") => if hd Args = bool then "hn_word"
                         else raise Fail ("unsupported fcp type " ^ type_to_string ty)
    | ("bool", "itself") => "unit"
    | ("finite_map", "fmap") => "(" ^ ml_ty (hd Args) ^ ", " ^ ml_ty (el 2 Args) ^ ") hn_fmap"
    | ("toto", "toto") => "(" ^ ml_ty (hd Args) ^ " -> " ^ ml_ty (hd Args) ^ " -> " ^
                          ml_ty ``:ordering`` ^ ")"
    | k => (case Redblackmap.peek (!datatype_tab, k) of
              NONE => raise Fail ("no ML type for " ^ type_to_string ty)
            | SOME i => let val name = "t" ^ Int.toString i ^ "_" ^ sanitize Tyop in
                case Args of
                  [] => name
                | _ => "(" ^ String.concatWith ", " (map ml_ty Args) ^ ") " ^ name end)
  end;

fun constructor_decl ty c = let
  val c = Term.inst (match_type (snd (strip_fun (type_of c))) ty) c
  val (args, _) = strip_fun (type_of c)
  val name = ml_name "K" (key c)
in case args of
     [] => name
   | _ => name ^ " of " ^ String.concatWith " * " (map ml_ty args) end;
fun datatype_decl i = let
  val (k, ty, cs) = Vector.sub (datatype_vec, i)
  val params = case snd (dest_type ty) of
      [] => ""
    | [a] => ml_tyvar a ^ " "
    | l => "(" ^ String.concatWith ", " (map ml_tyvar l) ^ ") "
in params ^ ml_ty ty |> (fn s => params ^ "t" ^ Int.toString i ^ "_" ^ sanitize (#2 k) ^ " =\n    " ^
     String.concatWith "\n  | " (map (constructor_decl ty) cs)) end;
fun datatype_deps i = let val (_, ty, cs) = Vector.sub (datatype_vec, i)
  in List.mapPartial (fn k => Redblackmap.peek (!datatype_tab, k))
       (List.foldl (fn (c, acc) => tyops (type_of c) acc) [] cs) end;
val datatype_text = String.concat (map (fn group =>
    "datatype " ^ String.concatWith "\nand " (map datatype_decl group) ^ "\n\n")
  (sccs (Vector.length datatype_vec) datatype_deps));
val () = pr ("datatypes: " ^ Int.toString (Vector.length datatype_vec) ^ "\n");

(* ---------- constant names ---------- *)
fun map_const is_con name c =
  ConstMapML.prim_insert (c, (is_con, "", name, type_of c));
val () = Vector.app (fn (_, _, cs) => List.app (fn c => map_const true (ml_name "K" (key c)) c) cs)
                    datatype_vec;
val () = map_const true "SOME" ``SOME``;
val () = map_const true "NONE" ``NONE``;
val () = List.app (fn (k, _) => map_const false (ml_name "c" k) (generic k)) normal_defs;
val () = Redblackmap.app (fn (k, ()) =>
    if is_result_width k orelse mem k [("words", "n2w"), ("words", "w2w"), ("words", "sw2sw"),
                                       ("fcp", "dimindex"), ("words", "dimword")]
    then () else map_const false (native_ml_name k) (generic k)) (!natives_used);

(* Natives whose result depends on a word width taken from their type. *)
val indexed_natives =
  [(("words", "n2w"), true), (("words", "w2w"), true), (("words", "sw2sw"), true),
   (("integer_word", "i2w"), true), (("words", "concat_word_list"), true),
   (("byte", "word_of_bytes_be"), true), (("bitstring", "v2w"), true),
   (("fcp", "dimindex"), false), (("words", "dimword"), false)];
val indexed_decls : string list ref = ref [];
val unindexed : string list ref = ref [];
fun index_const owner c =
  case List.find (fn (k, _) => k = key c) indexed_natives of
    NONE => ()
  | SOME (k, by_result) => let
      val ty = type_of c
      val wty = if by_result then snd (strip_fun ty)
                else wordsSyntax.mk_word_type (hd (snd (dest_type (fst (dom_rng ty)))))
    in case concrete_width wty of
         NONE => unindexed := (show k ^ " at " ^ type_to_string ty ^ " in " ^ owner) :: !unindexed
       | SOME w => let val name = native_ml_name k ^ "__" ^ Int.toString w
                   in if mem ("val " ^ name ^ " = " ^ native_ml_name k ^ " " ^ Int.toString w)
                            (!indexed_decls) then ()
                      else indexed_decls := ("val " ^ name ^ " = " ^ native_ml_name k ^ " " ^
                                             Int.toString w) :: !indexed_decls;
                      map_const false name c end
    end;
val () = List.app (fn (k, eqs) => List.app (fn eq => List.app (index_const (show k))
                    (find_terms is_const eq)) eqs) normal_defs;
val () = List.app (fn (h, tm) => List.app (index_const h) (find_terms is_const tm)) fixture_terms;
val () = pr ("width-polymorphic natives (" ^ Int.toString (length (!unindexed)) ^ "):\n  " ^
             String.concatWith "\n  " (Lib.mk_set (!unindexed)) ^ "\n");

(* ---------- printing ---------- *)
val () = EmitML.is_int_literal_hook := (fn _ => false);
val def_index = List.foldl (fn ((i, (k, _)), d) => Redblackmap.insert (d, k, i))
  (Redblackmap.mkDict key_cmp) (Lib.enumerate 0 normal_defs);
val def_vec = Vector.fromList normal_defs;
fun def_deps i = List.mapPartial (fn c => Redblackmap.peek (def_index, key c))
  (List.concat (map (find_terms is_const o rhs) (#2 (Vector.sub (def_vec, i)))));
fun pp_defn tm = PP.pp_to_string 100 (EmitML.pp_defn_as_ML []) tm;
fun pp_term tm = PP.pp_to_string 100 (EmitML.pp_term_as_ML [] EmitML.RIGHT) tm;
val failed = ref 0;
fun group_text group = let
  val t0 = Time.now ()
  val r = group_text0 group
  val dt = Time.toReal (Time.- (Time.now (), t0))
in if dt > 0.5 then pr ("slow group " ^ Real.toString dt ^ "s: " ^
     String.concatWith " " (map (show o #1 o fn i => Vector.sub (def_vec, i)) group) ^ "\n") else ();
   r end
and group_text0 group =
  (pp_defn (list_mk_conj (List.concat (map (#2 o fn i => Vector.sub (def_vec, i)) group))) ^ "\n\n")
  handle e => (failed := !failed + 1;
               pr ("PRINT FAIL " ^ String.concatWith " " (map (show o #1 o fn i => Vector.sub (def_vec, i)) group) ^
                   ": " ^ General.exnMessage e ^ "\n"); "");
val def_groups = sccs (Vector.length def_vec) def_deps;
val () = pr ("def groups: " ^ Int.toString (length def_groups) ^ ", largest " ^
  Int.toString (List.foldl Int.max 0 (map length def_groups)) ^ "\n");
val defs_text = String.concat (map group_text def_groups);
val fixtures_text =
  "val fixtures = [\n" ^ String.concatWith ",\n" (map (fn (h, tm) =>
    "  (" ^ Lib.mlquote h ^ ", fn () => " ^ pp_term tm ^ ")") fixture_terms) ^ "]\n";
val lits_text = String.concat (map (fn (t, v) => "val " ^ v ^ " = " ^ t ^ "\n") (rev (!lit_decls)));
(* Theory builds run in the script's directory; loading the script from the
   project root must not leave a copy of the module there. *)
val output_dir =
  if (OS.FileSys.access ("compilerNativeEmitScript.sml", [OS.FileSys.A_READ])
      handle OS.SysErr _ => false) then "."
  else "lowering/defs/bytecode/native";
val generated_path = OS.Path.concat (output_dir, module_name ^ "ML.sml");
val () = let val o' = TextIO.openOut generated_path in
  TextIO.output (o', "(* Generated by compilerNativeEmitScript.sml.  Do not edit. *)\n" ^
    "structure " ^ module_name ^ "ML = struct\nopen compilerNativeRuntime\n\n" ^
    datatype_text ^ lits_text ^ "\n" ^ String.concatWith "\n" (rev (!indexed_decls)) ^ "\n\n" ^
    defs_text ^ fixtures_text ^ "end\n");
  TextIO.closeOut o' end;
val () = pr ("print failures: " ^ Int.toString (!failed) ^ "\n");
val () = if !failed = 0 then () else raise Fail "EmitML could not print some equations";
