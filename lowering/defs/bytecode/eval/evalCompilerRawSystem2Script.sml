(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystem2
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../raw-system"]
val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
val fixture_root = "../raw-system/oracle"

val rl01_0topics = memoryStoreWitnessLib.evaluate fixture_root "rl01_0topics"
Theorem rl01_0topics_matches_python_oracle:
  ^(#term rl01_0topics) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl01_0topics")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl01_0topics))) >> EVAL_TAC
QED

val rl06_storage_data = memoryStoreWitnessLib.evaluate fixture_root "rl06_storage_data"
Theorem rl06_storage_data_matches_python_oracle:
  ^(#term rl06_storage_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl06_storage_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl06_storage_data))) >> EVAL_TAC
QED

val rr01_literal = memoryStoreWitnessLib.evaluate fixture_root "rr01_literal"
Theorem rr01_literal_matches_python_oracle:
  ^(#term rr01_literal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr01_literal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr01_literal))) >> EVAL_TAC
QED

val sd03_terminus_ret = memoryStoreWitnessLib.evaluate fixture_root "sd03_terminus_ret"
Theorem sd03_terminus_ret_matches_python_oracle:
  ^(#term sd03_terminus_ret) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "sd03_terminus_ret")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation sd03_terminus_ret))) >> EVAL_TAC
QED

val ctor01_rawlog = memoryStoreWitnessLib.evaluate fixture_root "ctor01_rawlog"
Theorem ctor01_rawlog_matches_python_oracle:
  ^(#term ctor01_rawlog) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "ctor01_rawlog")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation ctor01_rawlog))) >> EVAL_TAC
QED

