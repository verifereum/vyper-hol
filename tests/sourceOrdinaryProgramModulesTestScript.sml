Theory sourceOrdinaryProgramModulesTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.take (List.drop (sourceOrdinaryAcceptanceLib.rows,12),6));
val () = app sourceOrdinaryProgramTestLib.witness
  ["keccak_literal","len_string_lit","method_id_b4","method_id_bytes","method_id_const","method_id_storage"];
