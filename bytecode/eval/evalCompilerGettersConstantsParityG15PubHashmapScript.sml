(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG15PubHashmap
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g15_pub_hashmap = memoryStoreWitnessLib.evaluate fixture_root "g15_pub_hashmap"
Theorem g15_pub_hashmap_matches_python_oracle:
  ^(#term g15_pub_hashmap) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g15_pub_hashmap")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g15_pub_hashmap))) >> EVAL_TAC
QED
