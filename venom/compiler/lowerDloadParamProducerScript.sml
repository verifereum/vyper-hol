Theory lowerDloadParamProducer
Ancestors
  lowerDloadOpaqueExecution lowerDloadOwnership lowerDloadMaskBounds
  ptrDiscipline venomExecSemantics venomInst venomState finite_map list pred_set

Theorem ld_param_backward:
  i.inst_opcode = PARAM /\ i.inst_operands = [Lit idx] /\
  i.inst_outputs = [out] /\
  LENGTH AP = LENGTH s.vs_params /\ LENGTH BP = LENGTH t.vs_params /\
  LENGTH s.vs_params = LENGTH t.vs_params /\
  (!q. q < LENGTH s.vs_params ==>
    ld_owned_value E (EL q AP) (EL q BP) {} {}
      (EL q s.vs_params) (EL q t.vs_params)) /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel CT i t = OK t' ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    s' = update_var out (EL (w2n idx) s.vs_params) s /\
    t' = update_var out (EL (w2n idx) t.vs_params) t /\
    w2n idx < LENGTH s.vs_params /\
    ld_owned_vars U E (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t' /\
    (!v. v IN V ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuel CT i t = OK t'` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
  reverse conj_tac >- metis_tac[ld_lookup_defined_update] >>
  simp[ld_step_prov_def, ld_out_prov_def] >>
  irule ld_owned_vars_update_supported >>
  goal_assum (drule_at Any) >>
  simp[step_taint_def, out_taint_def, eval_operand_def] >>
  qexistsl_tac [`{}`, `{}`] >> simp[]
QED
