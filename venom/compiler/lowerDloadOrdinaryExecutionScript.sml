Theory lowerDloadOrdinaryExecution
Ancestors
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline
  venomExecSemantics venomState

Theorem ld_owned_assign_backward:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_owned_vars V E AG AH tn un s t /\ (!v. op = Var v ==> v IN V) /\
  step_inst fuelT CT i t = OK t' ==>
  ?x y s'. eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
    s' = update_var out x s /\ t' = update_var out y t /\
    step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `eval_operand op t` >> simp[] >> strip_tac >>
  `eval_operand op s = NONE <=> eval_operand op t = NONE` by
    metis_tac[ld_owned_operand_defined] >>
  Cases_on `eval_operand op s` >> gvs[] >>
  drule_all ld_owned_operand_value >> strip_tac >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  Cases_on `ld_op_prov AG op` >> Cases_on `ld_op_prov AH op` >>
  simp[ld_step_prov_def, ld_out_prov_def, ld_first_prov_def,
       step_taint_def, out_taint_def, ld_owned_vars_def, op_taint_def]
QED
