(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG31PubHashmapDynarrayVal
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g31_pub_hashmap_dynarray_val = memoryStoreWitnessLib.evaluate fixture_root "g31_pub_hashmap_dynarray_val"
Theorem g31_pub_hashmap_dynarray_val_matches_python_oracle:
  ^(#term g31_pub_hashmap_dynarray_val) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g31_pub_hashmap_dynarray_val")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g31_pub_hashmap_dynarray_val))) >> EVAL_TAC
QED
