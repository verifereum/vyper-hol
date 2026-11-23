(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsRcr05RawcreateArgs
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

val rcr05_rawcreate_args = memoryStoreWitnessLib.evaluate fixture_root "rcr05_rawcreate_args"
Theorem rcr05_rawcreate_args_matches_python_oracle:
  ^(#term rcr05_rawcreate_args) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rcr05_rawcreate_args")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rcr05_rawcreate_args))) >> EVAL_TAC
QED
