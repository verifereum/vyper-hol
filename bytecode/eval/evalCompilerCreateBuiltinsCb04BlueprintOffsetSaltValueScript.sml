(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb04BlueprintOffsetSaltValue
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

val cb04_blueprint_offset_salt_value = memoryStoreWitnessLib.evaluate fixture_root "cb04_blueprint_offset_salt_value"
Theorem cb04_blueprint_offset_salt_value_matches_python_oracle:
  ^(#term cb04_blueprint_offset_salt_value) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb04_blueprint_offset_salt_value")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb04_blueprint_offset_salt_value))) >> EVAL_TAC
QED
