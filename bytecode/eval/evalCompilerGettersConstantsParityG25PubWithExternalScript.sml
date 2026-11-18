(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG25PubWithExternal
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val g25_pub_with_external = memoryStoreWitnessLib.evaluate fixture_root "g25_pub_with_external"
Theorem g25_pub_with_external_matches_python_oracle:
  ^(#term g25_pub_with_external) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g25_pub_with_external")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g25_pub_with_external))) >> EVAL_TAC
QED
