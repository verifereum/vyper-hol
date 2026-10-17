(* Only non-CALL/non-STATICCALL primitives preserve the oracle lists.
 * Activated-call counterexamples live in venomCallActivationRegression.
 * INVOKE transport remains the calleeTransport boundary. *)
Theory oracleExecProps
Ancestors
  venomState venomInst venomExecSemantics oracleStateProps

Theorem step_inst_base_oracle:
  inst.inst_opcode <> CALL /\ inst.inst_opcode <> STATICCALL /\
  step_inst_base inst s = OK s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  PURE_REWRITE_TAC[step_inst_base_def] >>
  PURE_ASM_REWRITE_TAC[opcode_case_def] >>
  gvs[AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     istore_def, write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
QED

Theorem step_inst_noninvoke_oracle:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> CALL /\
  inst.inst_opcode <> STATICCALL /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_outcomes = s.vs_outcomes /\ s'.vs_requests = s.vs_requests
Proof
  simp[Once step_inst_def] >> strip_tac >> gvs[] >>
  drule step_inst_base_oracle >> simp[]
QED
