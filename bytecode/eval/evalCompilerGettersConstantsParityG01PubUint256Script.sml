(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG01PubUint256
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g01_pub_uint256 = memoryStoreWitnessLib.evaluate fixture_root "g01_pub_uint256"
Theorem g01_pub_uint256_matches_python_oracle:
  ^(#term g01_pub_uint256) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g01_pub_uint256")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g01_pub_uint256))) >> EVAL_TAC
QED
