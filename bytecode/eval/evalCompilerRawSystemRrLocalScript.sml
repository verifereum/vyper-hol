(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRrLocal
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

val rr_local = memoryStoreWitnessLib.evaluate fixture_root "rr_local"
Theorem rr_local_matches_python_oracle:
  ^(#term rr_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr_local))) >> EVAL_TAC
QED
