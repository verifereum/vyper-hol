(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityG13PubDynarray
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val g13_pub_dynarray = memoryStoreWitnessLib.evaluate fixture_root "g13_pub_dynarray"
Theorem g13_pub_dynarray_matches_python_oracle:
  ^(#term g13_pub_dynarray) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "g13_pub_dynarray")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation g13_pub_dynarray))) >> EVAL_TAC
QED
