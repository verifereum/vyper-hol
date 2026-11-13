(* Static observations of successful allocation-free decoder execution. *)
Theory abiValidAllocatedObservations
Ancestors
  ctorAbiActualWorld abiDecoderVarSequence venomExecSemantics venomState
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
