(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsRcr02RawcreateArgsSalt
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

val rcr02_rawcreate_args_salt = memoryStoreWitnessLib.evaluate fixture_root "rcr02_rawcreate_args_salt"
Theorem rcr02_rawcreate_args_salt_matches_python_oracle:
  ^(#term rcr02_rawcreate_args_salt) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rcr02_rawcreate_args_salt")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rcr02_rawcreate_args_salt))) >> EVAL_TAC
QED
