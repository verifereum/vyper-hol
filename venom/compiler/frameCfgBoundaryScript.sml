Theory frameCfgBoundary
Ancestors
  contextCodegenRel venomWf venomExecProps venomExecProofs
  venomExecSemantics venomState venomInst list

Theorem eval_phis_prev_bb:
  !s insts s'. eval_phis s insts = OK s' ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  Induct_on `insts` >> simp[eval_phis_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[update_var_def]
QED

Theorem enters_block_control_labels:
  enters_block fn s s1 ==>
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb
Proof
  simp[enters_block_def] >> rpt strip_tac >> gvs[] >>
  drule eval_phis_preserves_current_bb >>
  drule eval_phis_prev_bb >> simp[]
QED

Theorem extract_labels_filtered:
  !ops labels. extract_labels ops = SOME labels ==>
    MAP THE (FILTER IS_SOME (MAP get_label ops)) = labels
Proof
  Induct >> simp[extract_labels_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[extract_labels_def, get_label_def] >>
  Cases_on `extract_labels ops` >> simp[] >> metis_tac[]
QED

Theorem successful_terminator_successor:
  !inst s s'. is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def] >>
  gvs[step_inst_base_opcode_eqs, get_successors_def, get_label_def,
      jump_to_def, AllCaseEqs()] >>
  gvs[is_terminator_def] >>
  rpt (CHANGED_TAC (pairarg_tac >> gvs[])) >>
  IF_CASES_TAC >> simp[] >>
  drule extract_labels_filtered >> disch_then SUBST1_TAC >>
  simp[MEM_EL] >> metis_tac[]
QED

Theorem active_terminator_cfg_transition:
  wf_function fn /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
  enters_block fn s' s1 ==>
  fn_cfg_edge fn s.vs_current_bb s1.vs_current_bb /\
  s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  drule_all successful_terminator_successor >> strip_tac >>
  drule_all step_inst_base_term_prev_bb >> strip_tac >>
  drule enters_block_control_labels >> strip_tac >> gvs[] >>
  gvs[active_inst_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `EL s.vs_inst_idx bb.bb_instructions = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[LAST_EL]) >>
  simp[fn_cfg_edge_def] >> qexists_tac `bb` >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> gvs[MEM_nub, MEM_REVERSE]
QED
