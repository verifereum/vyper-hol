(* Independent checked-frontend bytecode witnesses for memory stores. *)
Theory evalCompilerMemoryStoreTuples
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

val t01_tuple_assign_intcall = memoryStoreWitnessLib.evaluate fixture_root "t01_tuple_assign_intcall"
Theorem t01_tuple_assign_intcall_matches_python_oracle:
  ^(#term t01_tuple_assign_intcall) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t01_tuple_assign_intcall")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t01_tuple_assign_intcall))) >> EVAL_TAC
QED

val t03_tuple_assign_abi_decode = memoryStoreWitnessLib.evaluate fixture_root "t03_tuple_assign_abi_decode"
Theorem t03_tuple_assign_abi_decode_matches_python_oracle:
  ^(#term t03_tuple_assign_abi_decode) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t03_tuple_assign_abi_decode")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t03_tuple_assign_abi_decode))) >> EVAL_TAC
QED

val t04_tuple_assign_extcall = memoryStoreWitnessLib.evaluate fixture_root "t04_tuple_assign_extcall"
Theorem t04_tuple_assign_extcall_matches_python_oracle:
  ^(#term t04_tuple_assign_extcall) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t04_tuple_assign_extcall")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t04_tuple_assign_extcall))) >> EVAL_TAC
QED

val t05_tuple_assign_storage_targets = memoryStoreWitnessLib.evaluate fixture_root "t05_tuple_assign_storage_targets"
Theorem t05_tuple_assign_storage_targets_matches_python_oracle:
  ^(#term t05_tuple_assign_storage_targets) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t05_tuple_assign_storage_targets")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t05_tuple_assign_storage_targets))) >> EVAL_TAC
QED

val t06_tuple_assign_mixed_targets = memoryStoreWitnessLib.evaluate fixture_root "t06_tuple_assign_mixed_targets"
Theorem t06_tuple_assign_mixed_targets_matches_python_oracle:
  ^(#term t06_tuple_assign_mixed_targets) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t06_tuple_assign_mixed_targets")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t06_tuple_assign_mixed_targets))) >> EVAL_TAC
QED

val t07_tuple_assign_string_elems = memoryStoreWitnessLib.evaluate fixture_root "t07_tuple_assign_string_elems"
Theorem t07_tuple_assign_string_elems_matches_python_oracle:
  ^(#term t07_tuple_assign_string_elems) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t07_tuple_assign_string_elems")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t07_tuple_assign_string_elems))) >> EVAL_TAC
QED

val t08_tuple_assign_ret_type_mismatch = memoryStoreWitnessLib.evaluate fixture_root "t08_tuple_assign_ret_type_mismatch"
Theorem t08_tuple_assign_ret_type_mismatch_matches_python_oracle:
  ^(#term t08_tuple_assign_ret_type_mismatch) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t08_tuple_assign_ret_type_mismatch")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t08_tuple_assign_ret_type_mismatch))) >> EVAL_TAC
QED

val t11_tuple_onew_decode_mem = memoryStoreWitnessLib.evaluate fixture_root "t11_tuple_onew_decode_mem"
Theorem t11_tuple_onew_decode_mem_matches_python_oracle:
  ^(#term t11_tuple_onew_decode_mem) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t11_tuple_onew_decode_mem")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t11_tuple_onew_decode_mem))) >> EVAL_TAC
QED

(* The b"ab" member is stored as a 256-bit word built by word_of_bytes, which
   EVAL computes with word_of_bytes_T_0w_256 in vyperMisc (#542). *)
val p16_return_tuple_bytes_widen = memoryStoreWitnessLib.evaluate fixture_root "p16_return_tuple_bytes_widen"
Theorem p16_return_tuple_bytes_widen_matches_python_oracle:
  ^(#term p16_return_tuple_bytes_widen) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p16_return_tuple_bytes_widen")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p16_return_tuple_bytes_widen))) >> EVAL_TAC
QED
