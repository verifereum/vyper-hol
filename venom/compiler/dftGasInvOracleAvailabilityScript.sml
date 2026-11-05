Theory dftGasInvOracleAvailability
Ancestors
  dftGasOracleDefs dftGasInvSSAProbe dftAvailability
  venomExecSemantics venomExecProofs venomInstProps venomState venomInst
  venomWf sccpCorrectnessProofs list finite_map pred_set option

Theorem inv_ev_step_not_phi:
  ev_step orc p d fuel ctx i s = OK t ==> i.inst_opcode <> PHI
Proof
  strip_tac >> strip_tac >>
  gvs[Once ev_step_def, step_inst_base_opcode_eqs]
QED

Theorem inv_ev_step_fdom_mono:
  ev_step orc p d fuel ctx i s = OK t /\ inst_wf i ==>
  FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  strip_tac >> Cases_on `is_terminator i.inst_opcode`
  >- (`step_inst fuel ctx i s = OK t` by
        (Cases_on `i.inst_opcode` >>
         gvs[is_terminator_def, Once ev_step_def, Once step_inst_def]) >>
      drule_all step_terminator_preserves_vars >> strip_tac >>
      simp[SUBSET_DEF] >> rpt strip_tac >>
      irule lookup_var_fdom >> qexists_tac `s` >> metis_tac[]) >>
  drule inv_ev_step_not_phi >> strip_tac >>
  drule_all inv_ev_step_availability >> simp[SUBSET_DEF]
QED

Theorem inv_ev_block_fdom_mono:
  !s t. ev_block orc p d fuel ctx bb s = OK t /\
    EVERY inst_wf bb.bb_instructions ==>
    FDOM s.vs_vars SUBSET FDOM t.vs_vars
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >> rename1 `OK mid` >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
  simp[] >> strip_tac
  >- (gvs[AllCaseEqs()] >> irule inv_ev_step_fdom_mono >>
      goal_assum (drule_at Any) >> fs[EVERY_EL]) >>
  `FDOM s.vs_vars SUBSET FDOM mid.vs_vars` by
    (irule inv_ev_step_fdom_mono >> goal_assum (drule_at Any) >> fs[EVERY_EL]) >>
  `FDOM mid.vs_vars SUBSET FDOM t.vs_vars` by
    (first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
     simp[] >> disch_then (qspec_then `mid with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
     simp[]) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem inv_ev_block_output:
  !s t idx v.
    ev_block orc p d fuel ctx bb s = OK t /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx <= idx /\ idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    MEM v (EL idx bb.bb_instructions).inst_outputs ==>
    v IN FDOM t.vs_vars
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >> simp[get_instruction_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >> rename1 `OK mid` >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
  simp[] >> strip_tac
  >- (`s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
        (fs[bb_well_formed_def] >> metis_tac[]) >>
      `idx = s.vs_inst_idx` by decide_tac >> gvs[]) >>
  Cases_on `s.vs_inst_idx = idx`
  >- (gvs[] >> rename1 `MEM outvar _.inst_outputs` >>
      `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by fs[EVERY_EL] >>
      drule inv_ev_step_not_phi >> strip_tac >>
      drule_all inv_ev_step_availability >> strip_tac >>
      `outvar IN FDOM mid.vs_vars` by simp[] >>
      drule inv_ev_block_fdom_mono >> simp[] >>
      simp[SUBSET_DEF]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then (qspec_then `mid with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> qexists_tac `idx` >> simp[]
QED

Theorem inv_ev_block_initialized_outputs:
  ev_block orc p d fuel ctx bb s = OK t /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  (!i v. i < s.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
     MEM v (EL i bb.bb_instructions).inst_outputs ==> v IN FDOM s.vs_vars) ==>
  !i v. i < LENGTH bb.bb_instructions /\
    ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
    MEM v (EL i bb.bb_instructions).inst_outputs ==> v IN FDOM t.vs_vars
Proof
  rpt strip_tac >> Cases_on `i < s.vs_inst_idx`
  >- (drule inv_ev_block_fdom_mono >> simp[SUBSET_DEF] >> metis_tac[]) >>
  irule inv_ev_block_output >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem inv_ev_terminator_base[local]:
  is_terminator i.inst_opcode ==>
  ev_step orc p d fuel ctx i s = step_inst_base i s
Proof
  Cases_on `i.inst_opcode` >> simp[is_terminator_def, Once ev_step_def]
QED

Theorem inv_ev_block_successor:
  !s t. ev_block orc p d fuel ctx bb s = OK t /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions ==>
    MEM t.vs_current_bb (bb_succs bb)
Proof
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >> simp[get_instruction_def] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  Cases_on `ev_step orc p d fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >> rename1 `OK mid` >>
  Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
  simp[] >> strip_tac
  >- (gvs[AllCaseEqs()] >>
      `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
        (fs[bb_well_formed_def] >> metis_tac[]) >>
      `inst_wf (EL s.vs_inst_idx bb.bb_instructions)` by fs[EVERY_EL] >>
      `step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s = OK mid` by
        metis_tac[inv_ev_terminator_base] >>
      drule_all step_inst_base_term_succs >> strip_tac >>
      simp[bb_succs_def] >>
      Cases_on `bb.bb_instructions` >> gvs[LAST_EL, MEM_nub, MEM_REVERSE]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[] >>
  disch_then (qspec_then `mid with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[]
QED

Theorem inv_ev_successor_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  strict_dom_vars_defined fn s /\ EVERY inst_wf bb.bb_instructions /\
  eval_phis s bb.bb_instructions = OK u /\
  ev_block orc p d fuel ctx bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t /\
  ~t.vs_halted ==>
  fn_reachable fn t.vs_current_bb /\ strict_dom_vars_defined fn t
Proof
  strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (irule inv_ev_block_successor >> simp[] >> goal_assum (drule_at Any)) >>
  `fn_cfg_edge fn s.vs_current_bb t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[fn_reachable_step] >>
  irule dft_dominance_transfer >> simp[] >>
  qexistsl_tac [`bb`, `s`] >> simp[] >>
  drule_all eval_phis_vars_grow >> strip_tac >>
  drule_all inv_ev_block_fdom_mono >> simp[] >> strip_tac >>
  reverse conj_tac >- metis_tac[SUBSET_TRANS] >>
  rpt strip_tac >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst`
    by metis_tac[MEM_EL] >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[terminator_no_outputs, EVERY_MEM, MEM] >>
  `!j w. j < phi_prefix_length bb.bb_instructions /\
     j < LENGTH bb.bb_instructions /\
     MEM w (EL j bb.bb_instructions).inst_outputs ==> w IN FDOM u.vs_vars` by
    (rpt strip_tac >> irule eval_phis_outputs_in_fdom_mem >>
     qexistsl_tac [`EL j bb.bb_instructions`, `bb.bb_instructions`, `s`] >>
     simp[] >> simp[MEM_EL] >> qexists_tac `j` >>
     simp[EL_TAKE, phi_prefix_length_le]) >>
  drule inv_ev_block_initialized_outputs >> simp[] >>
  disch_then (qspecl_then [`i`, `v`] mp_tac) >> simp[] >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >>
    qexists_tac `i'` >> simp[]) >> simp[]
QED

Theorem inv_ev_step_output:
  ev_step orc p d fuel ctx i s = OK t /\ inst_wf i /\
  MEM v i.inst_outputs ==> v IN FDOM t.vs_vars
Proof
  strip_tac >> Cases_on `is_terminator i.inst_opcode`
  >- (drule_all terminator_no_outputs >> strip_tac >> gvs[]) >>
  drule inv_ev_step_not_phi >> strip_tac >>
  drule_all inv_ev_step_availability >> simp[]
QED
