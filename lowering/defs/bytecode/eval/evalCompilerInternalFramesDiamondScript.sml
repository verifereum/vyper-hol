(* Independent pinned-byte regression for shared callee memory in a diamond. *)
Theory evalCompilerInternalFramesDiamond
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../internal-frames"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])

(* Metadata order is not ordered-set order. Both sets below contain the
   shared callee allocations; the analysis input must normalize that order. *)
Theorem diamond_shared_import_intersection:
  sinter alloc_to
    (incr_ssort alloc_to [Allocation 21; Allocation 64; Allocation 66; Allocation 67; Allocation 41; Allocation 43])
    (incr_ssort alloc_to [Allocation 17; Allocation 21; Allocation 22; Allocation 52; Allocation 54; Allocation 55; Allocation 41; Allocation 43]) =
    [Allocation 21; Allocation 41; Allocation 43]
Proof
  EVAL_TAC
QED

val fixture_root = "../internal-frames/oracle"
val p10_int_diamond = memoryStoreWitnessLib.evaluate fixture_root "p10_int_diamond"
Theorem p10_int_diamond_matches_python_oracle:
  ^(#term p10_int_diamond) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p10_int_diamond")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p10_int_diamond))) >> EVAL_TAC
QED
