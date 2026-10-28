(* Source-only fixed #543 fixtures and kernel certificates. Deliberately no
   lowering/correctness dependencies: backend failures are separate owners. *)
structure sourceMeaningLocationFixturesLib = struct
open HolKernel Parse boolLib bossLib
open sourceModuleElaborateTheory sourceModuleDefsTheory sourceSyntaxTheory
open sourceModuleEnvTheory vyperASTTheory finite_mapTheory
fun read path = let val stream = TextIO.openIn path in
  TextIO.inputAll stream before TextIO.closeIn stream end;
val names = String.tokens Char.isSpace
  (read "../lowering/defs/bytecode/folded-value-witnesses.txt");
val () = if List.length names = 37 then () else raise Fail "#543 manifest changed";
fun slots name = if name = "method_id_storage" then ``[((NONE,"m"),0:num)]:storage_layout``
  else if name = "i12_immut_with_storage" then ``[((NONE,"s"),0:num)]:storage_layout``
  else ``[]:storage_layout``;
fun trust name = let val sl = slots name in
  ``<| smt_ids := [(["main"],NONE)]; smt_nominals := [];
       smt_type_defs := FEMPTY; smt_slots := ^sl |>`` end;
fun program name = JSONDecode.decodeFile sourceSyntaxLib.annotated_ast
  ("fixtures/check_contract/source_syntax/" ^ name ^ ".json");
fun certified_phase name = let val p = program name val tr = trust name
  val suffix = if name = "method_id_var" then "_reject" else "_ast"
  val th = DB.fetch "sourceModuleFrontendLibTest" ("source_module_" ^ name ^ suffix)
  val () = if aconv (lhs(concl th)) ``source_module_elaborate_simple 80 ^tr [["main"]] ^p``
    then () else raise Fail ("stale original source certificate: " ^ name)
  in th end;
fun tops name = let
  val retained = hd(#2(strip_comb(rhs(concl(certified_phase name)))))
  val entries = #1(listSyntax.dest_list(List.nth(#2(strip_comb retained),1)))
  in case entries of [entry] => let val (src,tops) = pairSyntax.dest_pair entry in
    if optionSyntax.is_none src then tops else raise Fail "non-main witness module" end
  | _ => raise Fail "non-single witness module" end;
fun audit thy = let val exports = DB.thms thy
  val () = if null exports then raise Fail ("empty audit: " ^ thy) else ()
  in List.app (fn (name,th) => let val (oracles,axioms) = Tag.dest_tag(Thm.tag th)
    in if null(hyp th) andalso null axioms andalso List.all (fn s => s = "DISK_THM") oracles
      then () else raise Fail ("source location kernel audit: " ^ thy ^ "." ^ name) end) exports;
    print("SOURCE_LOCATION_KERNEL_CLOSED " ^ thy ^ " exports=" ^ Int.toString(List.length exports) ^ "\n")
  end;
end
