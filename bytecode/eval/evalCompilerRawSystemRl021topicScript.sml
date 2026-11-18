(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRl021topic
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

val rl02_1topic = memoryStoreWitnessLib.evaluate fixture_root "rl02_1topic"
Theorem rl02_1topic_matches_python_oracle:
  ^(#term rl02_1topic) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl02_1topic")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl02_1topic))) >> EVAL_TAC
QED
