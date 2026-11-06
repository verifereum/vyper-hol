(* Independent checked-frontend bytecode witnesses for the load-timing
   fixtures (tests/fixtures/load_timing): when a value read from storage or
   memory is taken, relative to later operands that modify it. *)
Theory evalCompilerLoadTiming
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../../../../tests/fixtures/load_timing"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../../../../tests/fixtures/load_timing/oracle"

(* An internal-call argument read before a later argument pops the array. *)
val call_memory_pop = memoryStoreWitnessLib.evaluate fixture_root "call_memory_pop"
Theorem call_memory_pop_matches_python_oracle:
  ^(#term call_memory_pop) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "call_memory_pop")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation call_memory_pop))) >> EVAL_TAC
QED
