(* Opcode-local world observations for actual-site decoder composition. *)
Theory ctorAbiActualWorld
Ancestors
  ctorAbiActualReentry abiDecoderVarSequence abiDecoderContract
  abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
  venomExecSemantics venomState venomInst venomMemDefs compileEnv exprLoweringProps
  finite_map list arithmetic

Theorem ctor_actual_step_world:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    exec_alloca_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
    jump_to_def]
QED

Theorem ctor_actual_sequence_world:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_pending_deletions = s.vs_pending_deletions
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all ctor_actual_step_world >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem ctor_actual_step_no_alloca:
  abi_decoder_reentry_opcode inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
  step_inst_base inst s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
    jump_to_def]
QED

Theorem ctor_actual_sequence_no_alloca:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    i.inst_opcode <> ALLOCA) code /\ run_inst_seq code s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all ctor_actual_step_no_alloca >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem ctor_actual_scratch_free_effect:
  abi_decode_frame d n s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_immutables = s.vs_immutables /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_pending_deletions = s.vs_pending_deletions ==>
  abi_encoder_registered_effect ids [(d,n)] s t /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv ctx fn site t <=> alloca_frontier_inv ctx fn site s)
Proof
  strip_tac >>
  conj_tac
  >- (gvs[abi_encoder_registered_effect_def, abi_decode_frame_def] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_def, remaining_alloca_budget_def]
QED
