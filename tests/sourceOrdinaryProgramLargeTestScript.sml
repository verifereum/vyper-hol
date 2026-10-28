Theory sourceOrdinaryProgramLargeTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.drop (sourceOrdinaryAcceptanceLib.rows,24));
val () = app sourceOrdinaryProgramTestLib.witness
  ["dec_unwrap_const","ctl03_abi_method_id","enc_ensT_uint_mid","neg_lit","pow_neglit_base","lt_mixed_lit"];
