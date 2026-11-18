(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityC09ConstBytes32
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val c09_const_bytes32 = memoryStoreWitnessLib.evaluate fixture_root "c09_const_bytes32"
Theorem c09_const_bytes32_matches_python_oracle:
  ^(#term c09_const_bytes32) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c09_const_bytes32")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c09_const_bytes32))) >> EVAL_TAC
QED
