(* Independent checked-frontend bytecode witnesses for memory stores.
   Half 1 of evalCompilerMemoryStoreTuples: t01_tuple_assign_intcall,
   t04_tuple_assign_extcall, t05_tuple_assign_storage_targets. *)
Theory evalCompilerMemoryStoreTuples1
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
