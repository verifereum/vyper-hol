(* Independent checked-frontend bytecode witnesses for memory stores. *)
Theory evalCompilerMemoryStoreContexts
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../memory-stores/oracle"

val r07_assert_storage_string_reason = memoryStoreWitnessLib.evaluate fixture_root "r07_assert_storage_string_reason"
Theorem r07_assert_storage_string_reason_matches_python_oracle:
  ^(#term r07_assert_storage_string_reason) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "r07_assert_storage_string_reason")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation r07_assert_storage_string_reason))) >> EVAL_TAC
QED

val p06_local_append_struct = memoryStoreWitnessLib.evaluate fixture_root "p06_local_append_struct"
Theorem p06_local_append_struct_matches_python_oracle:
  ^(#term p06_local_append_struct) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p06_local_append_struct")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p06_local_append_struct))) >> EVAL_TAC
QED

val p15_local_append_bytes = memoryStoreWitnessLib.evaluate fixture_root "p15_local_append_bytes"
Theorem p15_local_append_bytes_matches_python_oracle:
  ^(#term p15_local_append_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p15_local_append_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p15_local_append_bytes))) >> EVAL_TAC
QED

val p64_string_annassign_call = memoryStoreWitnessLib.evaluate fixture_root "p64_string_annassign_call"
Theorem p64_string_annassign_call_matches_python_oracle:
  ^(#term p64_string_annassign_call) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p64_string_annassign_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p64_string_annassign_call))) >> EVAL_TAC
QED

val e70_noData_live_mem2 = memoryStoreWitnessLib.evaluate fixture_root "e70_noData_live_mem2"
Theorem e70_noData_live_mem2_matches_python_oracle:
  ^(#term e70_noData_live_mem2) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "e70_noData_live_mem2")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation e70_noData_live_mem2))) >> EVAL_TAC
QED

val dec_from_memory2 = memoryStoreWitnessLib.evaluate fixture_root "dec_from_memory2"
Theorem dec_from_memory2_matches_python_oracle:
  ^(#term dec_from_memory2) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "dec_from_memory2")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation dec_from_memory2))) >> EVAL_TAC
QED
