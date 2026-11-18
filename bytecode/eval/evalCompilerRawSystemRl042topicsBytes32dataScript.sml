(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRl042topicsBytes32data
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-system"]
val () = compilerParityCompsetLib.prepare {byte_updates = true}
val fixture_root = "../raw-system/oracle"

val rl04_2topics_bytes32data = memoryStoreWitnessLib.evaluate fixture_root "rl04_2topics_bytes32data"
Theorem rl04_2topics_bytes32data_matches_python_oracle:
  ^(#term rl04_2topics_bytes32data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl04_2topics_bytes32data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl04_2topics_bytes32data))) >> EVAL_TAC
QED
