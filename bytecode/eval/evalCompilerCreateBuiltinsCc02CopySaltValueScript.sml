(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCc02CopySaltValue
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../create-builtins"]
val () = compilerParityCompsetLib.prepare {byte_updates = true}
val fixture_root = "../create-builtins/oracle"

val cc02_copy_salt_value = memoryStoreWitnessLib.evaluate fixture_root "cc02_copy_salt_value"
Theorem cc02_copy_salt_value_matches_python_oracle:
  ^(#term cc02_copy_salt_value) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cc02_copy_salt_value")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cc02_copy_salt_value))) >> EVAL_TAC
QED
