(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG21PubHashmapArrayVal
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val fixture_root = "../getters-constants/oracle"

val g21_pub_hashmap_array_val = memoryStoreWitnessLib.evaluate fixture_root "g21_pub_hashmap_array_val"
Theorem g21_pub_hashmap_array_val_matches_python_oracle:
  ^(#term g21_pub_hashmap_array_val) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g21_pub_hashmap_array_val")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g21_pub_hashmap_array_val))) >> EVAL_TAC
QED
