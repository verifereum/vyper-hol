(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb15BlueprintMembershipFlag
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../create-builtins"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../create-builtins/oracle"

val cb15_blueprint_membership_flag = memoryStoreWitnessLib.evaluate fixture_root "cb15_blueprint_membership_flag"
Theorem cb15_blueprint_membership_flag_matches_python_oracle:
  ^(#term cb15_blueprint_membership_flag) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb15_blueprint_membership_flag")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb15_blueprint_membership_flag))) >> EVAL_TAC
QED
