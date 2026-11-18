(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRr02Dynamic
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

val rr02_dynamic = memoryStoreWitnessLib.evaluate fixture_root "rr02_dynamic"
Theorem rr02_dynamic_matches_python_oracle:
  ^(#term rr02_dynamic) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr02_dynamic")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr02_dynamic))) >> EVAL_TAC
QED
