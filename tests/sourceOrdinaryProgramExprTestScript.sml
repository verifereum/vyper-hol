Theory sourceOrdinaryProgramExprTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.take (List.drop (sourceOrdinaryAcceptanceLib.rows,6),6));
val () = app sourceOrdinaryProgramTestLib.witness
  ["pow_folded_exp","pow_negfold_base","fold_cmp","fold_shift","fold_powmod","fold_addmod"];
