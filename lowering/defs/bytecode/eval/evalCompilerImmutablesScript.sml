(* Checked frontend inputs and exact pinned-Vyper deploy/runtime comparisons. *)
Theory evalCompilerImmutables
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  alist byte integer_word option vyperInterpreter
Libs
  memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../immutables"]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, i2w_def])
val fixture_root = "../immutables/oracle"

val p23_imm_uint256 = memoryStoreWitnessLib.evaluate fixture_root "p23_imm_uint256"
val p23_imm_uint256_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term p23_imm_uint256))``)
Theorem p23_imm_uint256_supported:
  supported_program ^(rand (#term p23_imm_uint256))
Proof
  ACCEPT_TAC p23_imm_uint256_supported_eval
QED

Theorem p23_imm_uint256_matches_python_oracle:
  ^(#term p23_imm_uint256) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p23_imm_uint256")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p23_imm_uint256))) >> EVAL_TAC
QED

Definition p23_source_deployment_def:
  p23_source_deployment =
    load_contract NONE [] initial_machine_state
      (empty_call_txn with
        <|target := 2w; sender := 1w; function_name := "__init__"|>)
      [(NONE, ^(rand (#term p23_imm_uint256)))] []
End

Theorem p23_source_deploy_get_42:
  ISL p23_source_deployment /\
  FST (call_external NONE [] (FST (OUTL p23_source_deployment))
    (empty_call_txn with
      <|target := 2w; sender := 1w; function_name := "get"|>)) = INL (IntV 42)
Proof
  EVAL_TAC
QED

val p24_imm_uint8 = memoryStoreWitnessLib.evaluate fixture_root "p24_imm_uint8"
val p24_imm_uint8_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term p24_imm_uint8))``)
Theorem p24_imm_uint8_supported:
  supported_program ^(rand (#term p24_imm_uint8))
Proof
  ACCEPT_TAC p24_imm_uint8_supported_eval
QED

Theorem p24_imm_uint8_matches_python_oracle:
  ^(#term p24_imm_uint8) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p24_imm_uint8")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p24_imm_uint8))) >> EVAL_TAC
QED

val p25_imm_address = memoryStoreWitnessLib.evaluate fixture_root "p25_imm_address"
val p25_imm_address_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term p25_imm_address))``)
Theorem p25_imm_address_supported:
  supported_program ^(rand (#term p25_imm_address))
Proof
  ACCEPT_TAC p25_imm_address_supported_eval
QED

Theorem p25_imm_address_matches_python_oracle:
  ^(#term p25_imm_address) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p25_imm_address")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p25_imm_address))) >> EVAL_TAC
QED

val p29b_imm_multi_nostr = memoryStoreWitnessLib.evaluate fixture_root "p29b_imm_multi_nostr"
val p29b_imm_multi_nostr_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term p29b_imm_multi_nostr))``)
Theorem p29b_imm_multi_nostr_supported:
  supported_program ^(rand (#term p29b_imm_multi_nostr))
Proof
  ACCEPT_TAC p29b_imm_multi_nostr_supported_eval
QED

Theorem p29b_imm_multi_nostr_matches_python_oracle:
  ^(#term p29b_imm_multi_nostr) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p29b_imm_multi_nostr")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p29b_imm_multi_nostr))) >> EVAL_TAC
QED

val p59_imm_with_runtime_internal = memoryStoreWitnessLib.evaluate fixture_root "p59_imm_with_runtime_internal"
val p59_imm_with_runtime_internal_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term p59_imm_with_runtime_internal))``)
Theorem p59_imm_with_runtime_internal_supported:
  supported_program ^(rand (#term p59_imm_with_runtime_internal))
Proof
  ACCEPT_TAC p59_imm_with_runtime_internal_supported_eval
QED

Theorem p59_imm_with_runtime_internal_matches_python_oracle:
  ^(#term p59_imm_with_runtime_internal) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "p59_imm_with_runtime_internal")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation p59_imm_with_runtime_internal))) >> EVAL_TAC
QED

val i01_immut_uint = memoryStoreWitnessLib.evaluate fixture_root "i01_immut_uint"
val i01_immut_uint_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term i01_immut_uint))``)
Theorem i01_immut_uint_supported:
  supported_program ^(rand (#term i01_immut_uint))
Proof
  ACCEPT_TAC i01_immut_uint_supported_eval
QED

Theorem i01_immut_uint_matches_python_oracle:
  ^(#term i01_immut_uint) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i01_immut_uint")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i01_immut_uint))) >> EVAL_TAC
QED

val i06_multiple_immutables = memoryStoreWitnessLib.evaluate fixture_root "i06_multiple_immutables"
val i06_multiple_immutables_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term i06_multiple_immutables))``)
Theorem i06_multiple_immutables_supported:
  supported_program ^(rand (#term i06_multiple_immutables))
Proof
  ACCEPT_TAC i06_multiple_immutables_supported_eval
QED

Theorem i06_multiple_immutables_matches_python_oracle:
  ^(#term i06_multiple_immutables) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i06_multiple_immutables")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i06_multiple_immutables))) >> EVAL_TAC
QED

val i08_immut_read_in_ctor = memoryStoreWitnessLib.evaluate fixture_root "i08_immut_read_in_ctor"
val i08_immut_read_in_ctor_supported_eval = EQT_ELIM
  (EVAL ``supported_program ^(rand (#term i08_immut_read_in_ctor))``)
Theorem i08_immut_read_in_ctor_supported:
  supported_program ^(rand (#term i08_immut_read_in_ctor))
Proof
  ACCEPT_TAC i08_immut_read_in_ctor_supported_eval
QED

Theorem i08_immut_read_in_ctor_matches_python_oracle:
  ^(#term i08_immut_read_in_ctor) =
    SOME ^(memoryStoreWitnessLib.oracle fixture_root "i08_immut_read_in_ctor")
Proof
  CONV_TAC (LAND_CONV (K (#evaluation i08_immut_read_in_ctor))) >> EVAL_TAC
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable parity fixture: " ^ name)
  end) (DB.thms "evalCompilerImmutables");
