(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb11BlueprintFoldedWeiOffset
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

val cb11_blueprint_folded_wei_offset = memoryStoreWitnessLib.evaluate fixture_root "cb11_blueprint_folded_wei_offset"
Theorem cb11_blueprint_folded_wei_offset_matches_python_oracle:
  ^(#term cb11_blueprint_folded_wei_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb11_blueprint_folded_wei_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb11_blueprint_folded_wei_offset))) >> EVAL_TAC
QED
