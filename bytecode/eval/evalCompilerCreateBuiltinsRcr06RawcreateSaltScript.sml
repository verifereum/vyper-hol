(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsRcr06RawcreateSalt
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

val rcr06_rawcreate_salt = memoryStoreWitnessLib.evaluate fixture_root "rcr06_rawcreate_salt"
Theorem rcr06_rawcreate_salt_matches_python_oracle:
  ^(#term rcr06_rawcreate_salt) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rcr06_rawcreate_salt")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rcr06_rawcreate_salt))) >> EVAL_TAC
QED
