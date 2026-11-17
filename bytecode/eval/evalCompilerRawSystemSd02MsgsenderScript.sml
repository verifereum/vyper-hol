(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystemSd02Msgsender
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

val sd02_msgsender = memoryStoreWitnessLib.evaluate fixture_root "sd02_msgsender"
Theorem sd02_msgsender_matches_python_oracle:
  ^(#term sd02_msgsender) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "sd02_msgsender")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation sd02_msgsender))) >> EVAL_TAC
QED
