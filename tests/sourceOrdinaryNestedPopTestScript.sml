Theory sourceOrdinaryNestedPopTest
Ancestors
  sourceOrdinaryExprProps sourceOrdinaryProgram sourceModuleElaborate
  sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib

fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];

(* Existing fixture, not a replacement oracle: exact independently translated
   AST/check artifact and deleted/poisoned fold metadata invariance. *)
val () = sourceOrdinaryProgramTestLib.ordinary ("nested_pop","nested_pop.json");
