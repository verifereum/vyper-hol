(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsRcr04RawcreateStorage
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

val rcr04_rawcreate_storage = memoryStoreWitnessLib.evaluate fixture_root "rcr04_rawcreate_storage"
Theorem rcr04_rawcreate_storage_matches_python_oracle:
  ^(#term rcr04_rawcreate_storage) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rcr04_rawcreate_storage")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rcr04_rawcreate_storage))) >> EVAL_TAC
QED
