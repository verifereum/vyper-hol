Theory sourceOrdinaryProgramRemainingTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.witness
  ["i12_immut_with_storage","p29_imm_multi","c16_const_string_in_expr","c27_const_binop_fold","rc09_abi_encode_data","rr03_abi"];
