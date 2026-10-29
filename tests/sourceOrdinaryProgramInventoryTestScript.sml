Theory sourceOrdinaryProgramInventoryTest
Ancestors
  sourceOrdinaryProgramCoreTest sourceOrdinaryProgramExprTest
  sourceOrdinaryProgramModulesTest sourceOrdinaryProgramPolicyTest
  sourceOrdinaryProgramLargeTest
Libs
  sourceOrdinaryFixtureLib

(* Current clean ordinary API.
   Every owner runs delete/poison through check_contract_result and compares
   modules, artifacts and both complete checker/composition equations. *)
val groups = [("sourceOrdinaryProgramCoreTest",0,6),
  ("sourceOrdinaryProgramExprTest",6,6),
  ("sourceOrdinaryProgramModulesTest",12,6),
  ("sourceOrdinaryProgramPolicyTest",18,6),
  ("sourceOrdinaryProgramLargeTest",24,3)];
val inventory = List.concat (map (fn (owner,start,count) => map
  (fn (name,_) => (owner,name))
  (List.take (List.drop (sourceOrdinaryFixtureLib.rows,start),count))) groups);
val () = if length inventory = 27 andalso
    length (List.foldl (fn ((_,name),names) =>
      if List.exists (fn n => n = name) names then names else name::names) [] inventory) = 27
  then () else raise Fail "ordinary current-27 inventory drift";
val () = app (fn (owner,name) => let
  val () = app (fn suffix => sourceOrdinaryFixtureLib.audit
    (DB.fetch owner (name ^ suffix)))
    ["_ordinary_phase","_ordinary_original","_ordinary_check",
     "_ordinary_expected_ast","_ordinary_legacy_artifact"]
  in print ("BRIDGE_INVENTORY " ^ name ^
    " exact-AST independent-artifact folds=delete/poison same-pipeline\n") end) inventory;
val () = print "BRIDGE_ALL_27_KERNEL_CLOSED exact-AST+artifact delete/poison\n";
