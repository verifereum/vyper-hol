Theory sourceOrdinaryProgramRuntimeTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.filter (fn (name,_) => List.exists (fn n => n = name)
    ["defaults_control","deployment","nonreentrant","transient_storage","abi_encode","daddy"])
    sourceOrdinaryAcceptanceLib.rows);
