Theory lowerDloadExplicitBase
Ancestors
  lowerDloadSharedState lowerDloadReadEffects lowerDloadScalarClosure
  lowerDloadOwnership lowerDloadOperand lowerDloadPairedBoundary
  venomExecSemantics venomState venomInst ptrDiscipline list words finite_map pred_set

Theorem ld_initial_fmp_backward:
  i.inst_opcode = INITIAL_FMP /\ ld_shared_state tn un s t /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' out w. step_inst fuelS CS i s = OK s' /\ i.inst_outputs = [out] /\
    s' = update_var out w s /\ t' = update_var out w t
Proof
  strip_tac >> drule ld_shared_state_environment >> strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexists_tac `t.vs_initial_fmp` >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> simp[]
QED

Theorem ld_owned_initial_fmp_backward:
  i.inst_opcode = INITIAL_FMP /\ ld_shared_state tn un s t /\
  ld_owned_vars V E AG AH tn un s t /\
  step_inst fuelT CT i t = OK t' ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_owned_vars V E (ld_step_prov AP AG L i) (ld_step_prov AQ AH M i)
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >> drule_all ld_initial_fmp_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >> gvs[] >>
  `!st ta. out_taint ta i st = {}` by
    (rpt gen_tac >> simp[out_taint_def] >> rpt CASE_TAC >> simp[]) >>
  `ld_owned_value E NONE NONE {} {} w w` by
    simp[ld_owned_value_def, ld_mask_word_def] >>
  drule_all ld_owned_vars_update >>
  disch_then (qspec_then `out` mp_tac) >>
  simp[ld_step_prov_def, ld_out_prov_def, step_taint_def, out_taint_def,
       ld_owned_vars_def, op_taint_def]
QED

Theorem ld_bump_backward:
  i.inst_opcode = BUMP /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuelT CT i t = OK t' ==>
  ?s' ptr next base sz. step_inst fuelS CS i s = OK s' /\
    i.inst_outputs = [ptr;next] /\
    s' = update_var next (word_add base sz) (update_var ptr base s) /\
    t' = update_var next (word_add base sz) (update_var ptr base t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst fuelT CT i t = OK t'` mp_tac >>
  simp[Once step_inst_non_invoke, SimpLHS] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`base_val`,`sz`] >>
  simp[Once step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def, opcode_case_def] >> simp[]
QED

Theorem ld_owned_bump_backward:
  i.inst_opcode = BUMP /\ ld_owned_vars V E AG AH tn un s t /\
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
  drule_all ld_bump_backward >>
  disch_then (qspecl_then [`fuelS`,`CS`] strip_assume_tac) >> gvs[] >>
  simp[ld_owned_vars_def, ld_step_prov_def, ld_out_prov_def,
       step_taint_def, ld_set_prov_def, set_var_taint_def,
       update_var_def, lookup_var_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  gvs[ld_owned_vars_def] >> rpt strip_tac >>
  Cases_on `v = next` >> gvs[ld_owned_value_def, ld_mask_word_def] >>
  Cases_on `v = ptr` >> gvs[ld_owned_value_def, ld_mask_word_def] >>
  qpat_x_assum `!v'. v' IN V ==> _` (qspec_then `v` mp_tac) >>
  simp[lookup_var_def, op_taint_def]
QED
