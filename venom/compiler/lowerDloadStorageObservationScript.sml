Theory lowerDloadStorageObservation
Ancestors
  venomExecSemantics stateEquiv venomState venomInst list pred_set

Theorem ld_storage_observation_backward:
  MEM i.inst_opcode [SLOAD; SSTORE; TLOAD; TSTORE] /\
  eval_operands i.inst_operands s = eval_operands i.inst_operands t /\
  observable_equiv s t /\
  s.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  step_inst_base i t = OK t' ==>
  ?s'. step_inst_base i s = OK s' /\ observable_equiv s' t' /\
    (MEM i.inst_opcode [SLOAD; TLOAD] ==>
      !v. MEM v i.inst_outputs ==> lookup_var v s' = lookup_var v t') /\
    (MEM i.inst_opcode [SSTORE; TSTORE] ==>
      s'.vs_vars = s.vs_vars /\ t'.vs_vars = t.vs_vars) /\
    (s' with <|vs_vars := s.vs_vars; vs_accounts := s.vs_accounts;
               vs_transient := s.vs_transient|>) = s /\
    (t' with <|vs_vars := t.vs_vars; vs_accounts := t.vs_accounts;
               vs_transient := t.vs_transient|>) = t /\
    (!v. ~MEM v i.inst_outputs ==> lookup_var v s' = lookup_var v s) /\
    (!v. ~MEM v i.inst_outputs ==> lookup_var v t' = lookup_var v t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >> simp[step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[eval_operands_def, AllCaseEqs()] >>
  gvs[observable_equiv_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def] >>
  simp[update_var_def, lookup_var_def, sstore_def, tstore_def,
       observable_equiv_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[venom_state_component_equality]
QED
