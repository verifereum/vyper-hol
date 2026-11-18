(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb09BlueprintFoldedOffset
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

val cb09_blueprint_folded_offset = memoryStoreWitnessLib.evaluate fixture_root "cb09_blueprint_folded_offset"
Theorem cb09_blueprint_folded_offset_matches_python_oracle:
  ^(#term cb09_blueprint_folded_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb09_blueprint_folded_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb09_blueprint_folded_offset))) >> EVAL_TAC
QED
