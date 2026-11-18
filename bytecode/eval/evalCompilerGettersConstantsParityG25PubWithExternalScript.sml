(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG25PubWithExternal
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g25_pub_with_external = memoryStoreWitnessLib.evaluate fixture_root "g25_pub_with_external"
Theorem g25_pub_with_external_matches_python_oracle:
  ^(#term g25_pub_with_external) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g25_pub_with_external")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g25_pub_with_external))) >> EVAL_TAC
QED
