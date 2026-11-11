Theory dftGasSimDominance
Ancestors
  dftGasSimEndpoint dftGasSimSuccessor cfgNormSupplySim
  sccpCorrectnessProofs venomExecProofs venomExecSemantics venomWf
  venomInst venomState list pred_set finite_map

Theorem ev_strict_dom_vars_defined_preserved_from_prefix:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\
  ev_block orc p d fuel C bb s = OK t /\
  s.vs_inst_idx <= LENGTH bb.bb_instructions /\
  strict_dom_vars_defined f s /\ fn_reachable f s.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions /\
  (!j w. j < s.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
         MEM w (EL j bb.bb_instructions).inst_outputs ==>
         w IN FDOM s.vs_vars) ==>
  strict_dom_vars_defined f t
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  simp[strict_dom_vars_defined_def] >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- (`d_bb = bb` by metis_tac[same_label_same_block] >> gvs[] >>
      `?idx. idx < LENGTH bb.bb_instructions /\
             EL idx bb.bb_instructions = d_inst` by metis_tac[MEM_EL] >>
      `~is_terminator d_inst.inst_opcode` by
        (strip_tac >> `d_inst.inst_outputs = []` by
           metis_tac[terminator_no_outputs, EVERY_MEM] >> gvs[]) >>
      irule ev_block_outputs_in_fdom_from_prefix >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `MEM t.vs_current_bb (bb_succs bb)` by
    (drule_all ev_block_current_bb_in_succs >> simp[]) >>
  `fn_cfg_edge f s.vs_current_bb t.vs_current_bb` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `fn_dominates f d_bb.bb_label s.vs_current_bb` by
    metis_tac[fn_dominates_predecessor] >>
  `v IN FDOM s.vs_vars` by
    (gvs[strict_dom_vars_defined_def] >> metis_tac[]) >>
  drule_all ev_block_fdom_mono >> simp[SUBSET_DEF]
QED

Theorem ev_strict_dom_vars_defined_block_entry:
  wf_function f /\ MEM bb f.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  ev_block orc p d fuel C bb
    (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK t /\
  strict_dom_vars_defined f s /\ fn_reachable f s.vs_current_bb /\
  EVERY inst_wf bb.bb_instructions ==>
  strict_dom_vars_defined f t
Proof
  strip_tac >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  irule ev_strict_dom_vars_defined_preserved_from_prefix >>
  simp[] >>
  goal_assum (drule_at (Pat `ev_block _ _ _ _ _ _ _ = OK _`)) >>
  simp[phi_prefix_length_le] >>
  conj_tac
  >- (rpt strip_tac >> drule_all eval_phis_outputs_in_fdom_idx >> simp[]) >>
  drule_all strict_dom_vars_defined_eval_phis >> simp[]
QED
