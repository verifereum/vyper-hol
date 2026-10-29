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
Theorem e21_default_ret_matches_python_oracle:
  ^(#term e21_default_ret) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e21_default_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e21_default_ret))) >> EVAL_TAC
QED

val e22_static_default = memoryStoreWitnessLib.evaluate fixture_root "e22_static_default"
Theorem e22_static_default_matches_python_oracle:
  ^(#term e22_static_default) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e22_static_default")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e22_static_default))) >> EVAL_TAC
QED

val e30_default_ret_tuple = memoryStoreWitnessLib.evaluate fixture_root "e30_default_ret_tuple"
Theorem e30_default_ret_tuple_matches_python_oracle:
  ^(#term e30_default_ret_tuple) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e30_default_ret_tuple")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e30_default_ret_tuple))) >> EVAL_TAC
QED

val e37_default_ret_string = memoryStoreWitnessLib.evaluate fixture_root "e37_default_ret_string"
Theorem e37_default_ret_string_matches_python_oracle:
  ^(#term e37_default_ret_string) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e37_default_ret_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e37_default_ret_string))) >> EVAL_TAC
QED

val e38_default_ret_local_array = memoryStoreWitnessLib.evaluate fixture_root "e38_default_ret_local_array"
Theorem e38_default_ret_local_array_matches_python_oracle:
  ^(#term e38_default_ret_local_array) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e38_default_ret_local_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e38_default_ret_local_array))) >> EVAL_TAC
QED
