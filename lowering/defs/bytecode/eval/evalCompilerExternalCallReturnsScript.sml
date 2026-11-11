(* Independent checked-frontend bytecode witnesses for external-call result buffers. *)
Theory evalCompilerExternalCallReturns
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e04_ret_string = memoryStoreWitnessLib.evaluate fixture_root "e04_ret_string"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e04_ret_string" e04_ret_string

val e05_ret_bytes = memoryStoreWitnessLib.evaluate fixture_root "e05_ret_bytes"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "e05_ret_bytes" e05_ret_bytes
