(* Independent pinned-oracle regressions for issue #545 internal frames.
   Captures use VYPER_PIN with python_o1_bytecode_oracle.py settings.
   Half 2 of evalCompilerInternalFrames: p06_int_for_range, p09_int_chain,
   p39_int_local_clobber, p40_int_for_clobber, p41_int_local_and_call,
   p02_int_local_string, p47_len_of_string_call. *)
Theory evalCompilerInternalFrames2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps
  ["../internal-frames/oracle/p06_int_for_range.json",
   "../internal-frames/oracle/p06_int_for_range.hex",
   "../internal-frames/oracle/p09_int_chain.json",
   "../internal-frames/oracle/p09_int_chain.hex",
   "../internal-frames/oracle/p39_int_local_clobber.json",
   "../internal-frames/oracle/p39_int_local_clobber.hex",
   "../internal-frames/oracle/p40_int_for_clobber.json",
   "../internal-frames/oracle/p40_int_for_clobber.hex",
   "../internal-frames/oracle/p41_int_local_and_call.json",
   "../internal-frames/oracle/p41_int_local_and_call.hex",
   "../internal-frames/oracle/p02_int_local_string.json",
   "../internal-frames/oracle/p02_int_local_string.hex",
   "../internal-frames/oracle/p47_len_of_string_call.json",
   "../internal-frames/oracle/p47_len_of_string_call.hex"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])
val fixture_root = "../internal-frames/oracle"

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
