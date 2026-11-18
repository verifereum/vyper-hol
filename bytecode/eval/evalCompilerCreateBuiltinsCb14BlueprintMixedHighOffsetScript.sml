(* Exact checked-compiler deployment/runtime parity for create-builtins. *)
Theory evalCompilerCreateBuiltinsCb14BlueprintMixedHighOffset
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

val cb14_blueprint_mixed_high_offset = memoryStoreWitnessLib.evaluate fixture_root "cb14_blueprint_mixed_high_offset"
Theorem cb14_blueprint_mixed_high_offset_matches_python_oracle:
  ^(#term cb14_blueprint_mixed_high_offset) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "cb14_blueprint_mixed_high_offset")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation cb14_blueprint_mixed_high_offset))) >> EVAL_TAC
QED
