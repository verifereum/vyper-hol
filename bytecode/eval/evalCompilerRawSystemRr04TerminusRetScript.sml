(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRr04TerminusRet
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib compilerParityCompsetLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-system"]
val () = compilerParityCompsetLib.prepare {byte_updates = true}
val fixture_root = "../raw-system/oracle"

val rr04_terminus_ret = memoryStoreWitnessLib.evaluate fixture_root "rr04_terminus_ret"
Theorem rr04_terminus_ret_matches_python_oracle:
  ^(#term rr04_terminus_ret) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr04_terminus_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr04_terminus_ret))) >> EVAL_TAC
QED
