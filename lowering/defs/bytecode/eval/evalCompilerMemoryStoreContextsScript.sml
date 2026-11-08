(* Independent checked-frontend bytecode witnesses for memory stores. *)
Theory evalCompilerMemoryStoreContexts
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../memory-stores"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../memory-stores/oracle"

val p06_local_append_struct = memoryStoreWitnessLib.evaluate fixture_root "p06_local_append_struct"
Theorem p06_local_append_struct_matches_python_oracle:
  ^(#term p06_local_append_struct) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p06_local_append_struct")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p06_local_append_struct))) >> EVAL_TAC
QED

val dec_from_memory2 = memoryStoreWitnessLib.evaluate fixture_root "dec_from_memory2"
val () = memoryStoreWitnessLib.check_decoder_divergence fixture_root
  "dec_from_memory2" dec_from_memory2
