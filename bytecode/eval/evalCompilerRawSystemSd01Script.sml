(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemSd01
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

val sd01 = memoryStoreWitnessLib.evaluate fixture_root "sd01"
Theorem sd01_matches_python_oracle:
  ^(#term sd01) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "sd01")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation sd01))) >> EVAL_TAC
QED
