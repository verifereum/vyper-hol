(* Oracle representation is inert in the concrete primitive semantics.
 * INVOKE transport is handled by calleeTransport, not call activation. *)
Theory oracleExecProps
Ancestors
  venomState venomInst venomExecSemantics oracleStateProps

Theorem step_inst_base_oracle:
  step_inst_base inst s = OK s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     istore_def, write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
QED

Theorem step_inst_noninvoke_oracle:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  simp[Once step_inst_def] >> strip_tac >> gvs[] >>
  drule step_inst_base_oracle >> simp[]
QED
