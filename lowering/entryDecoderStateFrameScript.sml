(* Source observations carried by a single decoder endpoint. *)
Theory entryDecoderStateFrame
Ancestors
  entryDecoderObservations abiDecoderReentry abiDecoderVarExtend
  execEquivParamDefs abiDecoderVarSequence venomExecSemantics venomState
  venomInst exprLoweringProps list

Definition entry_decoder_obs_def:
  entry_decoder_obs s t <=>
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_labels = s.vs_labels /\ t.vs_fmp = s.vs_fmp
End

Theorem entry_decoder_obs_refl[simp]:
  entry_decoder_obs s s
Proof
  simp[entry_decoder_obs_def]
QED

Theorem entry_decoder_obs_trans:
  entry_decoder_obs s t /\ entry_decoder_obs t u ==> entry_decoder_obs s u
Proof
  simp[entry_decoder_obs_def]
QED

Theorem entry_decoder_obs_fmp:
  entry_decoder_obs s t ==> t.vs_fmp = s.vs_fmp
Proof
  simp[entry_decoder_obs_def]
QED

Theorem entry_decoder_obs_prune[simp]:
  entry_decoder_obs s (abi_decoder_prune_vars next t) <=> entry_decoder_obs s t
Proof
  simp[entry_decoder_obs_def, abi_decoder_prune_vars_def]
QED

Theorem entry_decoder_obs_vars_extend:
  abi_decoder_vars_extend extras s t ==> entry_decoder_obs s t
Proof
  simp_tac bool_ss [abi_decoder_vars_extend_def] >> strip_tac >>
  qpat_x_assum `abi_decoder_var_map _ _ _` kall_tac >>
  first_x_assum (fn th => map_every
    (fn q => assume_tac (SIMP_RULE (srw_ss()) [vsr_frame_def] (Q.AP_TERM q th)))
    [`\s:venom_state. s.vs_accounts`, `\s:venom_state. s.vs_transient`,
     `\s:venom_state. s.vs_logs`, `\s:venom_state. s.vs_call_ctx`,
     `\s:venom_state. s.vs_tx_ctx`, `\s:venom_state. s.vs_block_ctx`,
     `\s:venom_state. s.vs_outcomes`, `\s:venom_state. s.vs_requests`,
     `\s:venom_state. s.vs_pending_deletions`, `\s:venom_state. s.vs_data_section`,
     `\s:venom_state. s.vs_gas_readings`, `\s:venom_state. s.vs_labels`,
     `\s:venom_state. s.vs_fmp`]) >>
  simp[entry_decoder_obs_def]
QED

Theorem entry_decoder_step_obs:
  abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  entry_decoder_obs s t
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[abi_decoder_reentry_opcode_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[entry_decoder_obs_def, update_var_def, mstore_def, mcopy_def,
      write_memory_with_expansion_def, jump_to_def] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def]
QED

Theorem entry_decoder_sequence_obs:
  !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
    run_inst_seq code s = OK t ==> entry_decoder_obs s t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  drule_all entry_decoder_step_obs >> strip_tac >>
  first_x_assum drule_all >>
  metis_tac[entry_decoder_obs_trans]
QED

Theorem entry_decoder_obs_cursor[simp]:
  entry_decoder_obs s
    (t with <|vs_prev_bb := prev; vs_current_bb := lbl; vs_inst_idx := idx|>) <=>
  entry_decoder_obs s t
Proof
  simp[entry_decoder_obs_def]
QED

Theorem entry_decoder_obs_inst_idx[simp]:
  entry_decoder_obs s (t with vs_inst_idx := idx) <=> entry_decoder_obs s t
Proof
  simp[entry_decoder_obs_def]
QED

Theorem entry_decoder_obs_update_var[simp]:
  entry_decoder_obs s (update_var name value t) <=> entry_decoder_obs s t
Proof
  simp[entry_decoder_obs_def, update_var_def]
QED

Theorem entry_decoder_obs_mstore[simp]:
  entry_decoder_obs s (mstore addr value t) <=> entry_decoder_obs s t
Proof
  simp[entry_decoder_obs_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem entry_decoder_obs_jump[simp]:
  entry_decoder_obs s (jump_to lbl t) <=> entry_decoder_obs s t
Proof
  simp[entry_decoder_obs_def, jump_to_def]
QED
