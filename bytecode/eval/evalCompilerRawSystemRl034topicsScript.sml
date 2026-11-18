(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRl034topics
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

val rl03_4topics = memoryStoreWitnessLib.evaluate fixture_root "rl03_4topics"
Theorem rl03_4topics_matches_python_oracle:
  ^(#term rl03_4topics) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl03_4topics")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl03_4topics))) >> EVAL_TAC
QED
