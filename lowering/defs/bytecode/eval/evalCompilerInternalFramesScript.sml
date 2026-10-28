(* Independent pinned-oracle regressions for issue #545 internal frames.
   Captures use VYPER_PIN with python_o1_bytecode_oracle.py settings. *)
Theory evalCompilerInternalFrames
Ancestors evalCompilerInternalFramesDiamond evalCompilerInternalFramesExtCall alist byte integer_word option
Libs memoryStoreWitnessLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../internal-frames"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])
val fixture_root = "../internal-frames/oracle"

val p01 = memoryStoreWitnessLib.evaluate fixture_root "p01_int_local_word"
Theorem p01_int_local_word_matches_python_oracle:
  ^(#term p01) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p01_int_local_word")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p01))) >> EVAL_TAC
QED

val p03 = memoryStoreWitnessLib.evaluate fixture_root "p03_int_local_array"
Theorem p03_int_local_array_matches_python_oracle:
  ^(#term p03) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p03_int_local_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p03))) >> EVAL_TAC
QED

val p04 = memoryStoreWitnessLib.evaluate fixture_root "p04_int_local_struct"
Theorem p04_int_local_struct_matches_python_oracle:
  ^(#term p04) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p04_int_local_struct")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p04))) >> EVAL_TAC
QED

val p06 = memoryStoreWitnessLib.evaluate fixture_root "p06_int_for_range"
Theorem p06_int_for_range_matches_python_oracle:
  ^(#term p06) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p06_int_for_range")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p06))) >> EVAL_TAC
QED

val p09 = memoryStoreWitnessLib.evaluate fixture_root "p09_int_chain"
Theorem p09_int_chain_matches_python_oracle:
  ^(#term p09) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p09_int_chain")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p09))) >> EVAL_TAC
QED

val p21 = memoryStoreWitnessLib.evaluate fixture_root "p21_for_body_call"
Theorem p21_for_body_call_matches_python_oracle:
  ^(#term p21) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p21_for_body_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p21))) >> EVAL_TAC
QED

val p39 = memoryStoreWitnessLib.evaluate fixture_root "p39_int_local_clobber"
Theorem p39_int_local_clobber_matches_python_oracle:
  ^(#term p39) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p39_int_local_clobber")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p39))) >> EVAL_TAC
QED

val p40 = memoryStoreWitnessLib.evaluate fixture_root "p40_int_for_clobber"
Theorem p40_int_for_clobber_matches_python_oracle:
  ^(#term p40) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p40_int_for_clobber")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p40))) >> EVAL_TAC
QED

val p41 = memoryStoreWitnessLib.evaluate fixture_root "p41_int_local_and_call"
Theorem p41_int_local_and_call_matches_python_oracle:
  ^(#term p41) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p41_int_local_and_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p41))) >> EVAL_TAC
QED

val p76 = memoryStoreWitnessLib.evaluate fixture_root "p76_int_assert_raise"
Theorem p76_int_assert_raise_matches_python_oracle:
  ^(#term p76) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p76_int_assert_raise")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p76))) >> EVAL_TAC
QED

val p92 = memoryStoreWitnessLib.evaluate fixture_root "p92_int_revert_branch"
Theorem p92_int_revert_branch_matches_python_oracle:
  ^(#term p92) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p92_int_revert_branch")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p92))) >> EVAL_TAC
QED

(* Ordered liveness allocation ties: internal String local and call-result len. *)
val p02 = memoryStoreWitnessLib.evaluate fixture_root "p02_int_local_string"
Theorem p02_int_local_string_matches_python_oracle:
  ^(#term p02) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p02_int_local_string")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p02))) >> EVAL_TAC
QED

val p47 = memoryStoreWitnessLib.evaluate fixture_root "p47_len_of_string_call"
Theorem p47_len_of_string_call_matches_python_oracle:
  ^(#term p47) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p47_len_of_string_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p47))) >> EVAL_TAC
QED
