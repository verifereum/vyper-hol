Theory lowerDloadReadEffects
Ancestors
  lowerDloadOrdinaryExecution lowerDloadPairedBoundary venomExecSemantics
  lowerDloadOwnership lowerDloadOperand ptrDiscipline venomInst list

Theorem ld_exec_pure2_backward:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  exec_pure2 f i t = OK t' ==>
  ?s' out w. exec_pure2 f i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t
Proof
  strip_tac >>
  qpat_x_assum `exec_pure2 _ _ _ = _` mp_tac >>
  simp[exec_pure2_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[exec_pure2_def] >> metis_tac[MEM]
QED

Theorem ld_owned_byte_backward:
  MEM i.inst_opcode [SIGNEXTEND; BYTE] /\
  i.inst_outputs = [out] /\ ld_owned_vars V E AG AH tn un s t /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  (!op. MEM op i.inst_operands ==> ld_op_prov AG op = NONE /\ op_taint tn op = {}) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_owned_operand_clean >> simp[] >> metis_tac[]) >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
  simp[MEM] >> strip_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> strip_tac >>
  (drule_all ld_exec_pure2_backward >> strip_tac >> gvs[] >>
   qexists_tac `update_var out w s` >>
   conj_tac
   >- (simp[Once step_inst_non_invoke] >>
       asm_rewrite_tac[step_inst_base_def, opcode_case_def]) >>
   `ld_owned_value E NONE NONE {} {} w w` by
     simp[ld_owned_value_def, ld_mask_word_def] >>
   drule_all ld_owned_vars_update >>
   disch_then (qspec_then `out` mp_tac) >>
   gvs[exec_pure2_def, AllCaseEqs()] >>
   simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
        ld_owned_vars_def, op_taint_def])
QED

Theorem ld_exec_read0_backward:
  f s = f t /\ exec_read0 f i t = OK t' ==>
  ?s' out w. exec_read0 f i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t
Proof
  simp[exec_read0_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qexists_tac `f t` >> simp[]
QED

Theorem ld_exec_read1_backward:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  (!w. f w s = f w t) /\ exec_read1 f i t = OK t' ==>
  ?s' out w. exec_read1 f i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t
Proof
  strip_tac >>
  qpat_x_assum `exec_read1 _ _ _ = _` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[exec_read1_def] >> metis_tac[MEM]
QED
