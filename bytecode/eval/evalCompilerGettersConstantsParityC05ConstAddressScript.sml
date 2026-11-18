(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityC05ConstAddress
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val c05_const_address = memoryStoreWitnessLib.evaluate fixture_root "c05_const_address"
Theorem c05_const_address_matches_python_oracle:
  ^(#term c05_const_address) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c05_const_address")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c05_const_address))) >> EVAL_TAC
QED
