(* Independent checked-frontend bytecode witnesses for default_return_value. *)
Theory evalCompilerExternalCallDefaults
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e21_default_ret = memoryStoreWitnessLib.evaluate fixture_root "e21_default_ret"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e21_default_ret" e21_default_ret

val e22_static_default = memoryStoreWitnessLib.evaluate fixture_root "e22_static_default"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e22_static_default" e22_static_default

val e30_default_ret_tuple = memoryStoreWitnessLib.evaluate fixture_root "e30_default_ret_tuple"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e30_default_ret_tuple" e30_default_ret_tuple

val e37_default_ret_string = memoryStoreWitnessLib.evaluate fixture_root "e37_default_ret_string"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e37_default_ret_string" e37_default_ret_string

val e38_default_ret_local_array = memoryStoreWitnessLib.evaluate fixture_root "e38_default_ret_local_array"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e38_default_ret_local_array" e38_default_ret_local_array
