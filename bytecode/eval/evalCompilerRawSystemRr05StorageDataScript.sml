(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRr05StorageData
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

val rr05_storage_data = memoryStoreWitnessLib.evaluate fixture_root "rr05_storage_data"
Theorem rr05_storage_data_matches_python_oracle:
  ^(#term rr05_storage_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr05_storage_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr05_storage_data))) >> EVAL_TAC
QED
