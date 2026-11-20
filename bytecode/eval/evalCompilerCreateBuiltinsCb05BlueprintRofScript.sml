(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb05BlueprintRof
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

val cb05_blueprint_rof = memoryStoreWitnessLib.evaluate fixture_root "cb05_blueprint_rof"
Theorem cb05_blueprint_rof_matches_python_oracle:
  ^(#term cb05_blueprint_rof) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb05_blueprint_rof")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb05_blueprint_rof))) >> EVAL_TAC
QED
