(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRl073topicsConcatNolit
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-system"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../raw-system/oracle"

val rl07_3topics_concat_nolit = memoryStoreWitnessLib.evaluate fixture_root "rl07_3topics_concat_nolit"
Theorem rl07_3topics_concat_nolit_matches_python_oracle:
  ^(#term rl07_3topics_concat_nolit) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl07_3topics_concat_nolit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl07_3topics_concat_nolit))) >> EVAL_TAC
QED
