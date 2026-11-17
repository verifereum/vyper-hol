(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemRl034topics
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

val rl03_4topics = memoryStoreWitnessLib.evaluate fixture_root "rl03_4topics"
Theorem rl03_4topics_matches_python_oracle:
  ^(#term rl03_4topics) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl03_4topics")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl03_4topics))) >> EVAL_TAC
QED
