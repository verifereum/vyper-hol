(* Independent external-state observation of scalar encoder execution. *)
Theory stmtSimLogExecFields
Ancestors
  exprLoweringProps venomExecSemantics venomMemDefs venomState venomInst finite_map words list

Definition log_encode_external_def:
  log_encode_external (s:venom_state) =
    s with <| vs_memory := []; vs_vars := FEMPTY;
              vs_allocas := FEMPTY; vs_alloca_next := 0 |>
End

Definition log_encode_safe_opcode_def:
  log_encode_safe_opcode opc <=>
    opc = ALLOCA \/ opc = ADD \/ opc = AND \/ opc = MLOAD \/
    opc = MSTORE \/ opc = MCOPY \/ opc = CALLDATASIZE \/ opc = CALLDATACOPY \/
    opc = NOT
End

Theorem log_encode_alloca_external[local]:
  exec_alloca i s n = OK t ==>
  log_encode_external t = log_encode_external s
Proof
  simp[exec_alloca_def, AllCaseEqs(), LET_THM] >> rpt strip_tac >>
  gvs[log_encode_external_def, update_var_def]
QED

Theorem log_encode_copy_external[local]:
  (i.inst_opcode = MCOPY \/ i.inst_opcode = CALLDATACOPY) /\
  step_inst_base i s = OK t ==>
  log_encode_external t = log_encode_external s
Proof
  strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs(), mcopy_def,
      write_memory_with_expansion_def, log_encode_external_def]
QED

Theorem log_encode_step_external:
  log_encode_safe_opcode i.inst_opcode /\ step_inst_base i s = OK t ==>
  log_encode_external t = log_encode_external s
Proof
  simp_tac bool_ss [log_encode_safe_opcode_def] >> strip_tac
  >- (gvs[step_inst_base_def, AllCaseEqs()] >>
      drule log_encode_alloca_external >> simp[])
  >- gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs(),
         log_encode_external_def, update_var_def]
  >- gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs(),
         log_encode_external_def, update_var_def]
  >- gvs[step_inst_base_def, exec_read1_def, AllCaseEqs(),
         log_encode_external_def, update_var_def]
  >- gvs[step_inst_base_def, exec_write2_def, AllCaseEqs(),
         mstore_def, write_memory_with_expansion_def, log_encode_external_def]
  >- (irule log_encode_copy_external >> qexists_tac `i` >> asm_simp_tac bool_ss [])
  >- gvs[step_inst_base_def, exec_read0_def, AllCaseEqs(),
         log_encode_external_def, update_var_def]
  >- (irule log_encode_copy_external >> qexists_tac `i` >> asm_simp_tac bool_ss []) >>
  gvs[step_inst_base_def, exec_pure1_def, AllCaseEqs(),
      log_encode_external_def, update_var_def]
QED

Theorem log_encode_run_external:
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  log_encode_external t = log_encode_external s
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  qexists_tac `code` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  irule log_encode_step_external >> qexists_tac `i` >>
  asm_simp_tac bool_ss [] >> fs[EVERY_MEM]
QED

Theorem log_encode_external_fields:
  log_encode_external t = log_encode_external s ==>
  t.vs_transient = s.vs_transient /\ t.vs_prev_bb = s.vs_prev_bb /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
  t.vs_returndata = s.vs_returndata /\ t.vs_halted = s.vs_halted /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_requests = s.vs_requests /\ t.vs_pending_deletions = s.vs_pending_deletions /\
  t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
  t.vs_labels = s.vs_labels /\ t.vs_code = s.vs_code /\ t.vs_params = s.vs_params /\
  t.vs_fmp = s.vs_fmp /\ t.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  t.vs_initial_fmp = s.vs_initial_fmp /\ t.vs_return_pc_token = s.vs_return_pc_token /\
  t.vs_prev_hashes = s.vs_prev_hashes
Proof
  simp[log_encode_external_def, venom_state_component_equality]
QED
