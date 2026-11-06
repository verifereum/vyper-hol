(* Independent checked-frontend bytecode witnesses for memory stores.
   Half 2 of evalCompilerMemoryStoreTuples: t06_tuple_assign_mixed_targets. *)
Theory evalCompilerMemoryStoreTuples2
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

val t06_tuple_assign_mixed_targets = memoryStoreWitnessLib.evaluate fixture_root "t06_tuple_assign_mixed_targets"
Theorem t06_tuple_assign_mixed_targets_matches_python_oracle:
  ^(#term t06_tuple_assign_mixed_targets) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "t06_tuple_assign_mixed_targets")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation t06_tuple_assign_mixed_targets))) >> EVAL_TAC
QED
