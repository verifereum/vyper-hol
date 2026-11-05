(* Independent checked-frontend bytecode witnesses for memory stores. *)
Theory evalCompilerMemoryStoreValues
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

val c03_annassign_empty_dynarray = memoryStoreWitnessLib.evaluate fixture_root "c03_annassign_empty_dynarray"
Theorem c03_annassign_empty_dynarray_matches_python_oracle:
  ^(#term c03_annassign_empty_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c03_annassign_empty_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c03_annassign_empty_dynarray))) >> EVAL_TAC
QED

val c04_annassign_empty_bytes = memoryStoreWitnessLib.evaluate fixture_root "c04_annassign_empty_bytes"
Theorem c04_annassign_empty_bytes_matches_python_oracle:
  ^(#term c04_annassign_empty_bytes) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c04_annassign_empty_bytes")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c04_annassign_empty_bytes))) >> EVAL_TAC
QED

val c06_assign_empty_storage_dynarray = memoryStoreWitnessLib.evaluate fixture_root "c06_assign_empty_storage_dynarray"
Theorem c06_assign_empty_storage_dynarray_matches_python_oracle:
  ^(#term c06_assign_empty_storage_dynarray) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "c06_assign_empty_storage_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c06_assign_empty_storage_dynarray))) >> EVAL_TAC
QED

val a09_local_array_from_storage = memoryStoreWitnessLib.evaluate fixture_root "a09_local_array_from_storage"
Theorem a09_local_array_from_storage_matches_python_oracle:
  ^(#term a09_local_array_from_storage) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "a09_local_array_from_storage")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation a09_local_array_from_storage))) >> EVAL_TAC
QED

val storage_one_word_array = memoryStoreWitnessLib.evaluate fixture_root "storage_one_word_array"
Theorem storage_one_word_array_matches_python_oracle:
  ^(#term storage_one_word_array) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "storage_one_word_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation storage_one_word_array))) >> EVAL_TAC
QED

val p20_nested_pop = memoryStoreWitnessLib.evaluate fixture_root "p20_nested_pop"
Theorem p20_nested_pop_matches_python_oracle:
  ^(#term p20_nested_pop) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p20_nested_pop")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p20_nested_pop))) >> EVAL_TAC
QED
