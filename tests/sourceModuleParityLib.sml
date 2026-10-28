(* Test-only source inputs. No legacy translator or oracle rewrite rules. *)
structure sourceModuleParityLib = struct
open HolKernel Parse boolLib bossLib
open sourceModuleCompileTheory sourceModuleElaborateTheory sourceModuleDefsTheory
open sourceSyntaxTheory vyperASTTheory finite_mapTheory

val base = "../lowering/defs/bytecode";
fun read path = let val s = TextIO.openIn path in
  TextIO.inputAll s before TextIO.closeIn s end;
val names = String.tokens Char.isSpace (read (base ^ "/folded-value-witnesses.txt"));
val seven = String.tokens Char.isSpace (read (base ^ "/folded-value-parity-fixtures.txt"));
val booleans = ["fold_not", "boolop_and3"];
val certified = seven @ booleans;
val () = if length names = 37 andalso length seven = 7 then ()
  else raise Fail "source parity inventory changed";
val address = ``0w:address``;
val keys = ``[["main"]]``;
fun slots name = if name = "method_id_storage" then ``[((NONE,"m"),0:num)]:storage_layout``
  else if name = "i12_immut_with_storage" then ``[((NONE,"s"),0:num)]:storage_layout``
  else ``[]:storage_layout``;
fun trust name = let val sl = slots name in
  ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
       smt_type_defs := FEMPTY; smt_slots := ^sl |>`` end;
fun layouts name = let val sl = slots name in ``[(^address,(^sl,[]:storage_layout))]`` end;
fun expected name = let
  val lines = String.tokens (fn c => c = #"\n")
    (read (base ^ "/folded-value-oracle/" ^ name ^ ".hex"))
  fun bytes key = let
    val line = valOf (List.find (String.isPrefix (key ^ "=")) lines)
    val hex = String.extract (line,size key + 1,NONE)
    fun digit c = if Char.isDigit c then Char.ord c - Char.ord #"0"
      else if #"a" <= c andalso c <= #"f" then Char.ord c - Char.ord #"a" + 10
      else raise Fail "invalid pinned hex"
    fun loop i = if i = size hex then [] else
      wordsSyntax.mk_wordii (16 * digit (String.sub (hex,i)) + digit (String.sub (hex,i+1)),8) :: loop (i+2)
    in listSyntax.mk_list (loop 0,type_of (wordsSyntax.mk_wordii (0,8))) end
  in pairSyntax.mk_pair (bytes "deploy",bytes "runtime") end;
fun program name = JSONDecode.decodeFile sourceSyntaxLib.annotated_ast
  ("fixtures/check_contract/source_syntax/" ^ name ^ ".json");
fun phase name = let val p = program name val tr = trust name in
  ``source_module_elaborate_simple 80 ^tr ^keys ^p`` end;
fun check name = let val p = program name val tr = trust name val ls = layouts name in
  ``source_module_check_simple 80 ^tr ^keys ^p ^ls ^address`` end;
fun compile name = let val p = program name val tr = trust name val ls = layouts name in
  ``source_module_compile 80 ^tr ^keys ^p ^ls ^address
      (K SOME) (o1_policy all_capabilities)`` end;

(* Reusing a kernel phase certificate is safe only at the identical freshly
   decoded original-source input, not merely at the same fixture name. *)
fun certified_phase name = let
  val suffix = if name = "method_id_var" then "_reject" else "_ast"
  val th = DB.fetch "sourceModuleFrontendLibTest" ("source_module_" ^ name ^ suffix)
  val () = if aconv (lhs (concl th)) (phase name) then ()
    else raise Fail ("stale source phase certificate: " ^ name)
  in th end;
fun certified_check name = let
  val th = DB.fetch "sourceModuleFrontendLibTest" ("source_module_" ^ name ^ "_composition")
  val () = if aconv (lhs (concl th)) (check name) then ()
    else raise Fail ("stale source checker certificate: " ^ name)
  in th end;
fun tops name = let
  val retained = hd (#2 (strip_comb (rhs (concl (certified_phase name)))))
  val modules = List.nth (#2 (strip_comb retained),1)
  val entries = #1 (listSyntax.dest_list modules)
  in case entries of [entry] => let val (src,tls) = pairSyntax.dest_pair entry in
    if optionSyntax.is_none src then tls else raise Fail "non-main module" end
  | _ => raise Fail "multiple modules" end;
fun wrapper name compiler = let
  val th = simpLib.SIMP_CONV (srw_ss())
    [source_module_compile_def,certified_check name,source_module_bind_def,
     retained_executable_def,compiler] (compile name)
  val head = #1 (strip_comb (rhs (concl th)))
  val () = if same_const head ``SM_Ok`` orelse same_const head ``SM_Error`` then ()
    else raise Fail ("residual source wrapper: " ^ name)
  in th end;
fun audit thy = app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then
      print ("SOURCE_PARITY_KERNEL_CLOSED " ^ thy ^ "." ^ name ^ " hyp=0\n")
    else raise Fail ("source parity kernel audit: " ^ thy ^ "." ^ name) end) (DB.thms thy);
end
