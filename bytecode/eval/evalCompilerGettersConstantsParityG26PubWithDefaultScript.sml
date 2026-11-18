(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG26PubWithDefault
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val g26_pub_with_default = memoryStoreWitnessLib.evaluate fixture_root "g26_pub_with_default"
Theorem g26_pub_with_default_matches_python_oracle:
  ^(#term g26_pub_with_default) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g26_pub_with_default")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g26_pub_with_default))) >> EVAL_TAC
QED
