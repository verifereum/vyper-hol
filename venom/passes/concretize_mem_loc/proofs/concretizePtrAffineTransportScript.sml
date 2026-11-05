Theory concretizePtrAffineTransport
Ancestors concretizePtrValueTransport ptrDiscipline venomState venomInst
  venomExecSemantics finite_map words list pred_set

Theorem ptr_vars_transport_update:
  ptr_vars_transport births positions TG tn s t /\
  ptr_value_transport births positions tag mask x y /\
  tn'.t_var = set_var_taint tn.t_var [out] mask ==>
  ptr_vars_transport births positions (set_prov TG [out] tag)
    tn'
    (update_var out x s) (update_var out y t)
Proof
  simp[ptr_vars_transport_def] >> rpt strip_tac >>
  Cases_on `v = out` >> Cases_on `tag` >>
  gvs[set_prov_def, set_var_taint_def, op_taint_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      ptr_lookup_transport_def]
QED

Theorem ptr_assign_transport:
  ptr_vars_transport births positions TG tn s t /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel C inst s = OK s' ==>
  ?t'. step_inst fuel C' inst t = OK t' /\
    ptr_vars_transport births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) s' t'
Proof
  strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG op) (op_taint tn op)
     (eval_operand op s) (eval_operand op t)` by
    (irule ptr_vars_transport_eval >> simp[]) >>
  gvs[Once run_defs, step_inst_base_def, AllCaseEqs()] >>
  gvs[ptr_lookup_transport_some] >>
  qexists_tac `update_var out z t` >>
  simp[Once run_defs, step_inst_base_def] >>
  simp[step_prov_def, out_prov_def, first_prov_def] >>
  irule ptr_vars_transport_update >>
  rpt (goal_assum (drule_at Any)) >>
  simp[step_taint_def, out_taint_def] >>
  qmatch_asmsub_abbrev_tac `ptr_value_transport births positions tag mask x y` >>
  qexists_tac `mask` >> Cases_on `tag` >> gvs[]
QED
