Theory lowerDloadOrdinaryExecution
Ancestors
  lowerDloadPairedBoundary lowerDloadOwnership ptrDiscipline
  venomExecSemantics venomState lowerDloadClassify lowerDloadControlPosition
  lowerDloadDefs o1ContractLowerDload

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

Theorem ld_owned_phis_backward:
  !ins s t t' AG AH tn un.
    ld_owned_vars V E AG AH tn un s t /\
    s.vs_prev_bb = t.vs_prev_bb /\
    (!i v. MEM i ins /\ MEM (Var v) i.inst_operands ==> v IN V) /\
    eval_phis t ins = OK t' ==>
    ?s'. eval_phis s ins = OK s' /\
      ld_owned_vars V E
        (ld_phis_prov s.vs_prev_bb AG ins)
        (ld_phis_prov t.vs_prev_bb AH ins)
        (tn with t_var := phis_taint s.vs_prev_bb tn ins)
        (un with t_var := phis_taint t.vs_prev_bb un ins) s' t'
Proof
  Induct >> rpt gen_tac >> simp[eval_phis_def, ld_phis_prov_def, phis_taint_def]
  >- simp[ld_owned_vars_def, op_taint_def] >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >> gvs[]
  >- (gvs[eval_one_phi_def, AllCaseEqs()] >>
      rename1 `eval_operand op t = SOME y` >>
      `!v. op = Var v ==> v IN V` by
        metis_tac[lowerDloadClassifyTheory.resolve_phi_MEM] >>
      `eval_operand op s = NONE <=> eval_operand op t = NONE` by
        metis_tac[ld_owned_operand_defined] >>
      Cases_on `eval_operand op s` >> gvs[] >>
      drule_all ld_owned_operand_value >> strip_tac >>
      first_x_assum (qspecl_then [`s`, `t`] mp_tac) >>
      disch_then drule >>
      disch_then (qspec_then `s''` mp_tac) >>
      simp[] >> impl_tac >- metis_tac[] >>
      strip_tac >>
      qexists_tac `update_var out x s'` >>
      conj_tac >- metis_tac[] >>
      drule_all ld_owned_vars_update >>
      disch_then (qspec_then `out` mp_tac) >>
      simp[ld_phi_prov_def, phi_taint_def]) >>
  gvs[ld_owned_vars_def, op_taint_def]
QED

Theorem ld_lowered_phis_annotations:
  !ins a outs b prev AG tn.
    lower_dload_insts_supply a ins = (outs,b) ==>
    ld_phis_prov prev AG outs = ld_phis_prov prev AG ins /\
    phis_taint prev tn outs = phis_taint prev tn ins
Proof
  Induct >- simp[lower_dload_insts_supply_def, ld_phis_prov_def, phis_taint_def] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`lower_dload_inst_supply a h = ([h],a)` by
        (irule lower_dload_inst_supply_special >> simp[]) >>
      gvs[] >> first_x_assum drule >>
      disch_then (qspecl_then [`prev`, `AG`, `tn`] strip_assume_tac) >>
      simp[ld_phis_prov_def, phis_taint_def]) >>
  `q <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  `MEM (HD q) q` by (Cases_on `q` >> gvs[]) >>
  `(HD q).inst_opcode <> PHI` by
    metis_tac[lower_dload_inst_supply_control] >>
  Cases_on `q` >> gvs[ld_phis_prov_def, phis_taint_def]
QED

Theorem ld_owned_lowered_block_phis_backward:
  lower_dload_block_supply a bb = (bb',b) /\
  ld_owned_vars V E AG AH tn un s t /\
  s.vs_prev_bb = t.vs_prev_bb /\
  (!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  eval_phis t bb'.bb_instructions = OK t' ==>
  ?s'. eval_phis s bb.bb_instructions = OK s' /\
    ld_owned_vars V E
      (ld_phis_prov s.vs_prev_bb AG bb.bb_instructions)
      (ld_phis_prov t.vs_prev_bb AH bb'.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb'.bb_instructions) s' t'
Proof
  strip_tac >>
  `eval_phis t bb.bb_instructions = OK t'` by
    metis_tac[lower_dload_block_supply_phis] >>
  `?a1. lower_dload_insts_supply a bb.bb_instructions = (bb'.bb_instructions,a1)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule ld_lowered_phis_annotations >>
  disch_then (qspecl_then [`t.vs_prev_bb`, `AH`, `un`] strip_assume_tac) >>
  drule_all ld_owned_phis_backward >> gvs[]
QED
