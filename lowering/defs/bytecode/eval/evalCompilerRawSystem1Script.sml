(* Exact checked-compiler deployment/runtime parity for raw-system. *)
Theory evalCompilerRawSystem1
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

val rl02_1topic = memoryStoreWitnessLib.evaluate fixture_root "rl02_1topic"
Theorem rl02_1topic_matches_python_oracle:
  ^(#term rl02_1topic) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl02_1topic")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl02_1topic))) >> EVAL_TAC
QED

val rl04_2topics_bytes32data = memoryStoreWitnessLib.evaluate fixture_root "rl04_2topics_bytes32data"
Theorem rl04_2topics_bytes32data_matches_python_oracle:
  ^(#term rl04_2topics_bytes32data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl04_2topics_bytes32data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl04_2topics_bytes32data))) >> EVAL_TAC
QED

val rl07_3topics_concat_nolit = memoryStoreWitnessLib.evaluate fixture_root "rl07_3topics_concat_nolit"
Theorem rl07_3topics_concat_nolit_matches_python_oracle:
  ^(#term rl07_3topics_concat_nolit) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rl07_3topics_concat_nolit")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rl07_3topics_concat_nolit))) >> EVAL_TAC
QED

val rr05_storage_data = memoryStoreWitnessLib.evaluate fixture_root "rr05_storage_data"
Theorem rr05_storage_data_matches_python_oracle:
  ^(#term rr05_storage_data) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "rr05_storage_data")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation rr05_storage_data))) >> EVAL_TAC
QED

val sd01 = memoryStoreWitnessLib.evaluate fixture_root "sd01"
Theorem sd01_matches_python_oracle:
  ^(#term sd01) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "sd01")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation sd01))) >> EVAL_TAC
QED

val sd02_msgsender = memoryStoreWitnessLib.evaluate fixture_root "sd02_msgsender"
Theorem sd02_msgsender_matches_python_oracle:
  ^(#term sd02_msgsender) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "sd02_msgsender")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation sd02_msgsender))) >> EVAL_TAC
QED

val sd04_if_then_continue = memoryStoreWitnessLib.evaluate fixture_root "sd04_if_then_continue"
Theorem sd04_if_then_continue_matches_python_oracle:
  ^(#term sd04_if_then_continue) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "sd04_if_then_continue")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation sd04_if_then_continue))) >> EVAL_TAC
QED

