(* Shared test-only original syntax, inherited layout and pinned bytecode.
   No full-Source frontend certificates or evaluator dependencies. *)
structure sourceBytecodeFixtureLib = struct
open HolKernel Parse boolLib bossLib
open sourceModuleDefsTheory sourceModuleEnvTheory
open sourceSyntaxTheory vyperASTTheory finite_mapTheory

val base = "../lowering/defs/bytecode";
fun read path = let val s = TextIO.openIn path in
  TextIO.inputAll s before TextIO.closeIn s end;
val names = String.tokens Char.isSpace (read (base ^ "/folded-value-witnesses.txt"));
val seven = String.tokens Char.isSpace (read (base ^ "/folded-value-parity-fixtures.txt"));
(* Independent expected checker outcomes for raw annotated-only inputs.
   #135 removed folded-value trust: x ** (1 + 2) must first normalize. *)
val legacy_outcomes =
  [("fold_add",true), ("pow_folded_exp",false), ("fold_cmp",true),
   ("enc_mid_const",true), ("fold_powmod",true), ("fold_addmod",true),
   ("fold_abs",true)];
val legacy_accepted = map #1 (List.filter #2 legacy_outcomes);
val booleans = ["fold_not", "boolop_and3"];
val certified = seven @ booleans;
(* Maintained inventory: source captures are local preparation, not oracles. *)
val () = if length names = 37 andalso length (Lib.mk_set names) = 37 then ()
  else raise Fail "fold validation manifest must enumerate 37 distinct witnesses";
val () = if length seven = 7 andalso Lib.set_eq seven
    ["fold_add", "pow_folded_exp", "fold_cmp", "enc_mid_const",
     "fold_powmod", "fold_addmod", "fold_abs"] andalso
    List.all (fn name => Lib.mem name names) seven then ()
  else raise Fail "required seven compatibility fixture sources are not prepared";
val () = if Lib.set_eq seven (map #1 legacy_outcomes) andalso
    length legacy_outcomes = 7 andalso length legacy_accepted = 6 then ()
  else raise Fail "legacy expected-outcome coverage differs from seven fixtures";
val source_dir = OS.FileSys.openDir (base ^ "/folded-value-sources");
fun entries dir = case OS.FileSys.readDir dir of
    NONE => [] | SOME s => s :: entries dir;
val source_files = entries source_dir before OS.FileSys.closeDir source_dir;
val () = if Lib.set_eq source_files (map (fn s => s ^ ".vy") names) then ()
  else raise Fail "fold validation source inventory differs from manifest";
val () = app (fn name =>
  if String.isSubstring "@external"
      (read (base ^ "/folded-value-sources/" ^ name ^ ".vy")) then ()
  else raise Fail ("missing external witness entry point: " ^ name)) names;
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
(* Reject NONE, residual computations and symbolic byte lists alike. *)
fun require_actual_byte_pair result = let
  val (deploy,runtime) = pairSyntax.dest_pair (optionSyntax.dest_some result)
  fun bytes tm = let
    val (items,ty) = listSyntax.dest_list tm
    in not (null items) andalso ty = type_of (wordsSyntax.mk_wordii (0,8))
      andalso List.all (fn item => can wordsSyntax.dest_word_literal item) items end
  in if null (free_vars result) andalso bytes deploy andalso bytes runtime then ()
    else raise Fail "expected SOME closed nonempty deployment/runtime byte lists" end;
fun program name = JSONDecode.decodeFile sourceSyntaxLib.annotated_ast
  ("fixtures/check_contract/source_syntax/" ^ name ^ ".json");
fun audit thy = app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles then
      print ("SOURCE_PARITY_KERNEL_CLOSED " ^ thy ^ "." ^ name ^ " hyp=0\n")
    else raise Fail ("source parity kernel audit: " ^ thy ^ "." ^ name) end) (DB.thms thy);
end
