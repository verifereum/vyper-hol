(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityC09ConstBytes32
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val c09_const_bytes32 = memoryStoreWitnessLib.evaluate fixture_root "c09_const_bytes32"
Theorem c09_const_bytes32_matches_python_oracle:
  ^(#term c09_const_bytes32) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c09_const_bytes32")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c09_const_bytes32))) >> EVAL_TAC
QED
