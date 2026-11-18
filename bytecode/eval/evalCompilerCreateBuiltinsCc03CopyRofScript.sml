(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCc03CopyRof
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

val cc03_copy_rof = memoryStoreWitnessLib.evaluate fixture_root "cc03_copy_rof"
Theorem cc03_copy_rof_matches_python_oracle:
  ^(#term cc03_copy_rof) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cc03_copy_rof")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cc03_copy_rof))) >> EVAL_TAC
QED
