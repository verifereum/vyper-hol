Theory sourceOrdinaryProgramCoreTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.take (sourceOrdinaryAcceptanceLib.rows,6));
val () = app sourceOrdinaryProgramTestLib.witness
  ["fold_add","fold_abs","fold_minmax","fold_not","boolop_and3","fold_pow_lit"];
