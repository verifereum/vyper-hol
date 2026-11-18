(* Independent checked-frontend deploy/runtime bytecode witnesses. *)
Theory evalCompilerGettersConstantsParityC26ConstArrayLocal
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../getters-constants/oracle"]
val () = compilerParityCompsetLib.prepare {byte_updates = false}
val fixture_root = "../getters-constants/oracle"

val c26_const_array_local = memoryStoreWitnessLib.evaluate fixture_root "c26_const_array_local"
Theorem c26_const_array_local_matches_python_oracle:
  ^(#term c26_const_array_local) = SOME ^(memoryStoreWitnessLib.oracle fixture_root "c26_const_array_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation c26_const_array_local))) >> EVAL_TAC
QED
