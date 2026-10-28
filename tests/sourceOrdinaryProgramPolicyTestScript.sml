Theory sourceOrdinaryProgramPolicyTest
Ancestors
  sourceOrdinaryProgram sourceModuleElaborate sourceModuleEnv vyperTypeContract vyperAST
Libs
  sourceOrdinaryProgramTestLib
fun holbuild_extra_deps (_:string list) = ();
val () = holbuild_extra_deps ["fixtures/check_contract","../lowering/defs/bytecode"];
val () = app sourceOrdinaryProgramTestLib.ordinary
  (List.take (List.drop (sourceOrdinaryAcceptanceLib.rows,18),6));
val () = app sourceOrdinaryProgramTestLib.witness
  ["enc_mid_const","enc_mid_methodid_call","enc_mid_bytes4lit","enc_ensF_string_mid","enc_ensF_uint_mid","enc_ensure_const"];
