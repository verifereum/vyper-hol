(* Independent checked-frontend bytecode witnesses for raw_call.
   Half 1 of evalCompilerRawCalls: rc25_stmt_argdata, rc02_outsize_ret,
   rc06_rof_false_bool, rc04_static, rc19_dyn_data, rc20_storage_data,
   rc07_rof_false_tuple. *)
Theory evalCompilerRawCalls1
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-calls"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../raw-calls/oracle"

val rc25_stmt_argdata = memoryStoreWitnessLib.evaluate fixture_root "rc25_stmt_argdata"
Theorem rc25_stmt_argdata_matches_python_oracle:
  ^(#term rc25_stmt_argdata) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc25_stmt_argdata")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc25_stmt_argdata))) >> EVAL_TAC
QED

val rc02_outsize_ret = memoryStoreWitnessLib.evaluate fixture_root "rc02_outsize_ret"
Theorem rc02_outsize_ret_matches_python_oracle:
  ^(#term rc02_outsize_ret) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc02_outsize_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc02_outsize_ret))) >> EVAL_TAC
QED

val rc06_rof_false_bool = memoryStoreWitnessLib.evaluate fixture_root "rc06_rof_false_bool"
Theorem rc06_rof_false_bool_matches_python_oracle:
  ^(#term rc06_rof_false_bool) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc06_rof_false_bool")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc06_rof_false_bool))) >> EVAL_TAC
QED

val rc04_static = memoryStoreWitnessLib.evaluate fixture_root "rc04_static"
Theorem rc04_static_matches_python_oracle:
  ^(#term rc04_static) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc04_static")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc04_static))) >> EVAL_TAC
QED

val rc19_dyn_data = memoryStoreWitnessLib.evaluate fixture_root "rc19_dyn_data"
Theorem rc19_dyn_data_matches_python_oracle:
  ^(#term rc19_dyn_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc19_dyn_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc19_dyn_data))) >> EVAL_TAC
QED

val rc20_storage_data = memoryStoreWitnessLib.evaluate fixture_root "rc20_storage_data"
Theorem rc20_storage_data_matches_python_oracle:
  ^(#term rc20_storage_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc20_storage_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc20_storage_data))) >> EVAL_TAC
QED

val rc07_rof_false_tuple = memoryStoreWitnessLib.evaluate fixture_root "rc07_rof_false_tuple"
Theorem rc07_rof_false_tuple_matches_python_oracle:
  ^(#term rc07_rof_false_tuple) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc07_rof_false_tuple")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc07_rof_false_tuple))) >> EVAL_TAC
QED
