(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsNest02StmtCreate
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

val nest02_stmt_create = memoryStoreWitnessLib.evaluate fixture_root "nest02_stmt_create"
Theorem nest02_stmt_create_matches_python_oracle:
  ^(#term nest02_stmt_create) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "nest02_stmt_create")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation nest02_stmt_create))) >> EVAL_TAC
QED
