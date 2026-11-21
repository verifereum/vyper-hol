(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRr03Abi
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

val rr03_abi = memoryStoreWitnessLib.evaluate fixture_root "rr03_abi"
Theorem rr03_abi_matches_python_oracle:
  ^(#term rr03_abi) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr03_abi")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr03_abi))) >> EVAL_TAC
QED
