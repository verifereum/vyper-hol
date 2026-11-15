(* Static observations of actual decoder prefixes and rejection witnesses. *)
Theory abiValidAllocatedObservations
Ancestors
  ctorAbiActualWorld abiDecoderVarSequence abiDecodePtrRejectChecks
  venomExecSemantics venomState
  venomInst venomMemDefs exprLoweringProps list arithmetic

Theorem abi_valid_allocated_step_static[local]:
  abi_decoder_reentry_opcode inst.inst_opcode /\
  step_inst_base inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
  t.vs_labels = s.vs_labels /\ t.vs_fmp = s.vs_fmp /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    exec_alloca_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
    jump_to_def] >>
  rpt IF_CASES_TAC >> simp[LENGTH_TAKE_EQ] >> decide_tac
QED

Theorem abi_valid_allocated_sequence_static:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
  t.vs_labels = s.vs_labels /\ t.vs_fmp = s.vs_fmp /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all abi_valid_allocated_step_static >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_valid_allocated_revert_observations:
  abi_decode_reject_witness code s u ==>
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables
Proof
  strip_tac >>
  qhdtm_assum `abi_decode_reject_witness`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_reject_witness_def]) >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all abi_valid_allocated_sequence_static >> strip_tac >>
  qpat_x_assum `abi_decoder_reentry_opcode bad.inst_opcode`
    (strip_assume_tac o REWRITE_RULE [abi_decoder_reentry_opcode_def, MEM]) >>
  gvs[] >>
  qpat_x_assum `step_inst_base bad r = Abort Revert_abort u` mp_tac >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs,
    exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    exec_alloca_def] >>
  strip_tac >> gvs[AllCaseEqs(), revert_state_def, halt_state_def,
    set_returndata_def]
QED
