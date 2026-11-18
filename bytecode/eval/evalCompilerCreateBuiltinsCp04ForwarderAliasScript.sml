(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCp04ForwarderAlias
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

val cp04_forwarder_alias = memoryStoreWitnessLib.evaluate fixture_root "cp04_forwarder_alias"
Theorem cp04_forwarder_alias_matches_python_oracle:
  ^(#term cp04_forwarder_alias) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cp04_forwarder_alias")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cp04_forwarder_alias))) >> EVAL_TAC
QED
