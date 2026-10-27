(* Independent pinned-oracle regressions for issue #545 internal frames.
   Captures use VYPER_PIN with python_o1_bytecode_oracle.py settings.
   Half 1 of evalCompilerInternalFrames: p01_int_local_word,
   p03_int_local_array, p04_int_local_struct, p21_for_body_call,
   p76_int_assert_raise, p92_int_revert_branch. *)
Theory evalCompilerInternalFrames1
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../internal-frames/oracle/p01_int_local_word.json",
   "../internal-frames/oracle/p01_int_local_word.hex",
   "../internal-frames/oracle/p03_int_local_array.json",
   "../internal-frames/oracle/p03_int_local_array.hex",
   "../internal-frames/oracle/p04_int_local_struct.json",
   "../internal-frames/oracle/p04_int_local_struct.hex",
   "../internal-frames/oracle/p21_for_body_call.json",
   "../internal-frames/oracle/p21_for_body_call.hex",
   "../internal-frames/oracle/p76_int_assert_raise.json",
   "../internal-frames/oracle/p76_int_assert_raise.hex",
   "../internal-frames/oracle/p92_int_revert_branch.json",
   "../internal-frames/oracle/p92_int_revert_branch.hex"]
val () = supportedEvalLib.configure ()
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

val p21 = memoryStoreWitnessLib.evaluate fixture_root "p21_for_body_call"
Theorem p21_for_body_call_matches_python_oracle:
  ^(#term p21) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "p21_for_body_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p21))) >> EVAL_TAC
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
