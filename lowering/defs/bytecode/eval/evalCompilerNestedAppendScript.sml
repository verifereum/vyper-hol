(* Checked pinned-Python bytecode witnesses for resolved append targets. *)
Theory evalCompilerNestedAppend
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

val p21_storage_field_append = memoryStoreWitnessLib.evaluate fixture_root "p21_storage_field_append"
Theorem p21_storage_field_append_matches_python_oracle:
  ^(#term p21_storage_field_append) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p21_storage_field_append")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p21_storage_field_append))) >> EVAL_TAC
QED

val p22_memory_field_append = memoryStoreWitnessLib.evaluate fixture_root "p22_memory_field_append"
Theorem p22_memory_field_append_matches_python_oracle:
  ^(#term p22_memory_field_append) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p22_memory_field_append")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p22_memory_field_append))) >> EVAL_TAC
QED

val p23_subscript_append = memoryStoreWitnessLib.evaluate fixture_root "p23_subscript_append"
Theorem p23_subscript_append_matches_python_oracle:
  ^(#term p23_subscript_append) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p23_subscript_append")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p23_subscript_append))) >> EVAL_TAC
QED

val p24_transient_field_append = memoryStoreWitnessLib.evaluate fixture_root "p24_transient_field_append"
Theorem p24_transient_field_append_matches_python_oracle:
  ^(#term p24_transient_field_append) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p24_transient_field_append")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p24_transient_field_append))) >> EVAL_TAC
QED

val p25_complex_field_append = memoryStoreWitnessLib.evaluate fixture_root "p25_complex_field_append"
Theorem p25_complex_field_append_matches_python_oracle:
  ^(#term p25_complex_field_append) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p25_complex_field_append")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p25_complex_field_append))) >> EVAL_TAC
QED

val p26_root_append = memoryStoreWitnessLib.evaluate fixture_root "p26_root_append"
Theorem p26_root_append_matches_python_oracle:
  ^(#term p26_root_append) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p26_root_append")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p26_root_append))) >> EVAL_TAC
QED
