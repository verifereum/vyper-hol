Theory vyperCheckContractSourceTest
Ancestors
  sourceModuleElaborate sourceModuleDefs vyperTypeContract vyperAST finite_map
Libs
  vyperCheckContractFrontendLib

(* The opt-in source route next to the default route. *)
fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/check_contract"]

val address = ``0w : address``;
val fixtures = "fixtures/check_contract/";
fun audit th = let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
  if null (hyp th) andalso null axioms andalso
     List.all (fn s => s = "DISK_THM") oracles then ()
  else raise Fail "source route theorem has assumptions, axioms or oracles" end;

(* The strict constant fixtures check to the same artifact on both routes. *)
val () = app (fn name => let
  val file = {address=address,path=fixtures ^ name ^ ".json"}
  val default = vyperCheckContractFrontendLib.check_constant_contract_file_legacy file
  val source = vyperCheckContractFrontendLib.Source.check_constant_contract_file file
  val () = app audit [default,source]
  val () = if aconv (rhs (concl source)) (rhs (concl default)) then ()
    else raise Fail ("source and default routes disagree: " ^ name)
  val _ = save_thm ("source_route_" ^ name,source)
in () end) ["constant_bound","constant_shifts"];

(* A pre-erasure loader capture of a two-module contract. *)
val loaded = vyperCheckContractFrontendLib.Source.check_contract_file_result
  {fuel=``40:num``,
   trust=``<| smt_ids := [(["main"],NONE);(["lib"],SOME 1)]; smt_nominals := [];
     smt_type_defs := FEMPTY; smt_slots := [((SOME 1,"stored"),0)] |>``,
   layouts=``[(0w:address,([((SOME 1,"stored"),0)]:storage_layout,[]:storage_layout))]``,
   address=address,path=fixtures ^ "source_loader/multimodule_storage.json"};
val () = app audit [#checking loaded,#composition loaded];
val _ = save_thm ("source_route_multimodule_storage",#checking loaded);
