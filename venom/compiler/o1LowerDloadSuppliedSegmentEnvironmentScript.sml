Theory o1LowerDloadSuppliedSegmentEnvironment
Ancestors
  o1LowerDloadEnvironment o1LowerDloadJointScalar o1LowerDloadOccurrence
  o1LowerDloadGhost ptrDiscipline venomState

Theorem ld_env_vars_cong:
  s1.vs_vars = s.vs_vars /\ t1.vs_vars = t.vs_vars /\
  ld_env_agree sites fn H tn s t ==>
  ld_env_agree sites fn H tn s1 t1
Proof
  simp[ld_env_agree_def]
QED

Theorem ld_env_supply_dload:
  ld_env_agree sites fn H tn s t /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\
  inst.inst_outputs = [out] /\
  ~MEM av (fn_ir_vars fn) /\ ~MEM bv (fn_ir_vars fn) /\
  s1 = update_var out x s /\
  t1.vs_vars = (update_var out x (update_var bv y (update_var av p t))).vs_vars ==>
  ld_env_agree sites fn (occurrence_step a HP H inst s1)
    (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >> gvs[] >>
  `ld_env_agree sites fn H tn s (update_var av p t)` by
    metis_tac[ld_env_fresh_target] >>
  `ld_env_agree sites fn H tn s (update_var bv y (update_var av p t))` by
    metis_tac[ld_env_fresh_target] >>
  irule ld_env_vars_cong >>
  qexistsl_tac [`update_var out x s`, `update_var out x (update_var bv y (update_var av p t))`] >>
  simp[] >> irule ld_env_clean_update >>
  simp[occurrence_out_def, out_prov_def, out_taint_def] >>
  Cases_on `eval_operand off s` >> simp[]
QED

Theorem ld_env_supply_dloadbytes:
  ld_env_agree sites fn H tn s t /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_outputs = [] /\
  s1.vs_vars = s.vs_vars /\ ~MEM bv (fn_ir_vars fn) /\
  t1.vs_vars = (update_var bv y t).vs_vars ==>
  ld_env_agree sites fn (occurrence_step a HP H inst s1)
    (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >>
  `ld_env_agree sites fn H tn s (update_var bv y t)` by
    metis_tac[ld_env_fresh_target] >>
  gvs[ld_env_agree_def, occurrence_step_def, set_prov_def,
      step_taint_def, set_var_taint_def, op_taint_def,
      finite_mapTheory.FLOOKUP_DRESTRICT]
QED
