(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb02BlueprintArgs
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

val cb02_blueprint_args = memoryStoreWitnessLib.evaluate fixture_root "cb02_blueprint_args"
Theorem cb02_blueprint_args_matches_python_oracle:
  ^(#term cb02_blueprint_args) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb02_blueprint_args")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb02_blueprint_args))) >> EVAL_TAC
QED
