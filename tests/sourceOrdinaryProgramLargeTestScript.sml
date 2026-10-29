Theory sourceOrdinaryProgramLargeTest
Ancestors
  sourceOrdinaryProgram sourceModuleContext sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.drop (sourceOrdinaryFixtureLib.rows,24));
