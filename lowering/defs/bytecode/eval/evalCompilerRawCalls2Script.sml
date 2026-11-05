(* Independent checked-frontend bytecode witnesses for raw_call.
   Half 2 of evalCompilerRawCalls: rc17_nested_len, rc22_bool_in_if,
   rc01_stmt_nooutsize, rc03_value_gas, rc21_internal_value_gas_order. *)
Theory evalCompilerRawCalls2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../raw-calls/oracle"

val rc17_nested_len = memoryStoreWitnessLib.evaluate fixture_root "rc17_nested_len"
Theorem rc17_nested_len_matches_python_oracle:
  ^(#term rc17_nested_len) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc17_nested_len")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc17_nested_len))) >> EVAL_TAC
QED

val rc22_bool_in_if = memoryStoreWitnessLib.evaluate fixture_root "rc22_bool_in_if"
Theorem rc22_bool_in_if_matches_python_oracle:
  ^(#term rc22_bool_in_if) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc22_bool_in_if")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc22_bool_in_if))) >> EVAL_TAC
QED

val rc01_stmt_nooutsize = memoryStoreWitnessLib.evaluate fixture_root "rc01_stmt_nooutsize"
Theorem rc01_stmt_nooutsize_matches_python_oracle:
  ^(#term rc01_stmt_nooutsize) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc01_stmt_nooutsize")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc01_stmt_nooutsize))) >> EVAL_TAC
QED

val rc03_value_gas = memoryStoreWitnessLib.evaluate fixture_root "rc03_value_gas"
Theorem rc03_value_gas_matches_python_oracle:
  ^(#term rc03_value_gas) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc03_value_gas")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc03_value_gas))) >> EVAL_TAC
QED

val rc21_internal_value_gas_order = memoryStoreWitnessLib.evaluate fixture_root "rc21_internal_value_gas_order"
Theorem rc21_internal_value_gas_order_matches_python_oracle:
  ^(#term rc21_internal_value_gas_order) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc21_internal_value_gas_order")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc21_internal_value_gas_order))) >> EVAL_TAC
QED
