(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG23PubTransientHashmap
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g23_pub_transient_hashmap = memoryStoreWitnessLib.evaluate fixture_root "g23_pub_transient_hashmap"
Theorem g23_pub_transient_hashmap_matches_python_oracle:
  ^(#term g23_pub_transient_hashmap) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g23_pub_transient_hashmap")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g23_pub_transient_hashmap))) >> EVAL_TAC
QED
