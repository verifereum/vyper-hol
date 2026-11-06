(* Independent checked-frontend bytecode witnesses for raw_call.
   Half 1 of evalCompilerRawCalls: rc06_rof_false_bool,
   rc20_storage_data. *)
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

val rc06_rof_false_bool = memoryStoreWitnessLib.evaluate fixture_root "rc06_rof_false_bool"
Theorem rc06_rof_false_bool_matches_python_oracle:
  ^(#term rc06_rof_false_bool) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc06_rof_false_bool")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc06_rof_false_bool))) >> EVAL_TAC
QED

val rc20_storage_data = memoryStoreWitnessLib.evaluate fixture_root "rc20_storage_data"
Theorem rc20_storage_data_matches_python_oracle:
  ^(#term rc20_storage_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rc20_storage_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rc20_storage_data))) >> EVAL_TAC
QED
