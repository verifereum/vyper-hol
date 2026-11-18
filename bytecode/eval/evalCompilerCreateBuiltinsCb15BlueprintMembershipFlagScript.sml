(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb15BlueprintMembershipFlag
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

val cb15_blueprint_membership_flag = memoryStoreWitnessLib.evaluate fixture_root "cb15_blueprint_membership_flag"
Theorem cb15_blueprint_membership_flag_matches_python_oracle:
  ^(#term cb15_blueprint_membership_flag) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb15_blueprint_membership_flag")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb15_blueprint_membership_flag))) >> EVAL_TAC
QED
