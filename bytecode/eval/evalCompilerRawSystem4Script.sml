(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystem4
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

val rr02_dynamic = memoryStoreWitnessLib.evaluate fixture_root "rr02_dynamic"
Theorem rr02_dynamic_matches_python_oracle:
  ^(#term rr02_dynamic) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr02_dynamic")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr02_dynamic))) >> EVAL_TAC
QED

val rr04_terminus_ret = memoryStoreWitnessLib.evaluate fixture_root "rr04_terminus_ret"
Theorem rr04_terminus_ret_matches_python_oracle:
  ^(#term rr04_terminus_ret) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr04_terminus_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr04_terminus_ret))) >> EVAL_TAC
QED

val rr_arg = memoryStoreWitnessLib.evaluate fixture_root "rr_arg"
Theorem rr_arg_matches_python_oracle:
  ^(#term rr_arg) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr_arg")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr_arg))) >> EVAL_TAC
QED

val rr_nr = memoryStoreWitnessLib.evaluate fixture_root "rr_nr"
Theorem rr_nr_matches_python_oracle:
  ^(#term rr_nr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr_nr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr_nr))) >> EVAL_TAC
QED

val rr_local = memoryStoreWitnessLib.evaluate fixture_root "rr_local"
Theorem rr_local_matches_python_oracle:
  ^(#term rr_local) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr_local")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr_local))) >> EVAL_TAC
QED
