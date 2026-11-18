(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb08BlueprintRuntimeOffset
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

val cb08_blueprint_runtime_offset = memoryStoreWitnessLib.evaluate fixture_root "cb08_blueprint_runtime_offset"
Theorem cb08_blueprint_runtime_offset_matches_python_oracle:
  ^(#term cb08_blueprint_runtime_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb08_blueprint_runtime_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb08_blueprint_runtime_offset))) >> EVAL_TAC
QED
