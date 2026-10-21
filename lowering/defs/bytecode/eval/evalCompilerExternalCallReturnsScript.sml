(* Independent checked-frontend bytecode witnesses for external-call result buffers. *)
Theory evalCompilerExternalCallReturns
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../external-calls"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../external-calls/oracle"

val e04_ret_string = memoryStoreWitnessLib.evaluate fixture_root "e04_ret_string"
Theorem e04_ret_string_matches_python_oracle:
  ^(#term e04_ret_string) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e04_ret_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e04_ret_string))) >> EVAL_TAC
QED

val e05_ret_bytes = memoryStoreWitnessLib.evaluate fixture_root "e05_ret_bytes"
Theorem e05_ret_bytes_matches_python_oracle:
  ^(#term e05_ret_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e05_ret_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e05_ret_bytes))) >> EVAL_TAC
QED
