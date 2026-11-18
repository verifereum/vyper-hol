(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsNest01CreateInCall
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

val nest01_create_in_call = memoryStoreWitnessLib.evaluate fixture_root "nest01_create_in_call"
Theorem nest01_create_in_call_matches_python_oracle:
  ^(#term nest01_create_in_call) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nest01_create_in_call")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nest01_create_in_call))) >> EVAL_TAC
QED
