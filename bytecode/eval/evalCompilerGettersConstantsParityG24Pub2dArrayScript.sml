(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG24Pub2dArray
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g24_pub_2d_array = memoryStoreWitnessLib.evaluate fixture_root "g24_pub_2d_array"
Theorem g24_pub_2d_array_matches_python_oracle:
  ^(#term g24_pub_2d_array) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g24_pub_2d_array")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g24_pub_2d_array))) >> EVAL_TAC
QED
