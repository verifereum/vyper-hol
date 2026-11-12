(* Whole-function observations and runs of a guarded bypass. *)
Theory simplifyCfgBypassSemantics
Ancestors
  simplifyCfgBypassPrefix simplifyCfgBypassTerminal simplifyCfgBypassRuns
  simplifyCfgBypassShape simplifyCfgBypassClosure simplifyCfgBypassPrecondition
  simplifyCfgBypassEntry simplifyCfgBypassStatic simplifyCfgBypassExec simplifyCfgMergeRuns
  simplifyCfgMergeGlobalRuns simplifyCfgFragments venomExecProps passSimulationDefs
  simplifyCfgControlExec simplifyCfgMergeSegment simplifyCfgLabelProps
  simplifyCfgStaticInterface simplifyCfgControl simplifyCfgDefs simplifyCfgSimTools
  venomExecSemantics venomExecProofs venomInst venomState venomWf cfgTransform
  o1PassLift contextCodegenRel stateFrame unitMemInv codegenRel list

Theorem scfg_bypass_initial_aligned:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 ==>
  scfg_bypass_aligned a b s0 s0
Proof
  strip_tac >>
  `first_block_no_preds fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_first_no_preds] >>
  `fn_entry_label fn <> SOME b.bb_label` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[scfg_bypass_not_entry]) >>
  fs[fn_entry_state_def, scfg_bypass_aligned_def, scfg_ctrl_def] >>
  conj_tac >- metis_tac[] >> simp[venom_state_component_equality]
QED

Theorem scfg_bypass_active_source_terminator:
  scfg_bypass_hyp fn a b fn' /\ active_inst fn i s /\
  s.vs_current_bb = a.bb_label /\ is_terminator i.inst_opcode ==>
  i.inst_opcode = JNZ
Proof
  strip_tac >>
  `wf_function fn` by
    metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
  drule_all scfg_active_terminator_last >> strip_tac >>
  `MEM a fn.fn_blocks` by
    (fs[scfg_bypass_hyp_def] >> metis_tac[lookup_block_member_label]) >>
  `bb = a` by metis_tac[same_label_same_block] >>
  drule scfg_bypass_source_shape >> strip_tac >> gvs[]
QED

Theorem scfg_bypass_image_observations:
  scfg_bypass_hyp fn a b fn' /\ active_inst fn i s /\
  scfg_bypass_aligned a b s t ==>
  mem_corr i s
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t /\
  call_corr i s
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t
Proof
  strip_tac >>
  `inst_wf i` by
    metis_tac[active_inst_wf, scfg_bypass_old_static, scfg_static_inst_wf] >>
  `scfg_payload s t` by fs[scfg_bypass_aligned_def, scfg_payload_def, scfg_ctrl_def] >>
  qmatch_goalsub_abbrev_tac `mem_corr i s j t` >>
  Cases_on `i.inst_opcode = PHI`
  >- suspend "phi" >>
  reverse (Cases_on `s.vs_current_bb = a.bb_label /\ is_terminator i.inst_opcode`)
  >- (`j = i` by
        (Cases_on `is_terminator i.inst_opcode`
         >- (fs[] >> simp[Abbr `j`, scfg_bypass_image_def, update_phi_bypass_def]) >>
         simp[Abbr `j`, scfg_bypass_image_ordinary]) >>
      metis_tac[scfg_payload_mem_corr, scfg_payload_call_corr]) >>
  `i.inst_opcode = JNZ` by metis_tac[scfg_bypass_active_source_terminator] >>
  `j.inst_opcode = JNZ \/ j.inst_opcode = JMP` by
    (simp[Abbr `j`] >> metis_tac[scfg_bypass_image_opcode]) >>
  gvs[mem_corr_def, call_corr_def, inst_mem_ranges_def, dalloca_no_wrap_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def,
      scfg_payload_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >> simp[scfg_ctrl_def]
QED

Resume scfg_bypass_image_observations[phi]:
  `j.inst_opcode = PHI` by
    (`i.inst_opcode <> JNZ` by simp[] >>
     simp[Abbr `j`] >> metis_tac[scfg_bypass_image_opcode]) >>
  gvs[mem_corr_def, call_corr_def, inst_mem_ranges_def, dalloca_no_wrap_def,
      source_memory_read_ranges_def, source_memory_write_ranges_def,
      scfg_payload_def] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >> simp[scfg_ctrl_def]
QED
Finalise scfg_bypass_image_observations
Theorem scfg_bypass_frame_sim:
  ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' ==> frame_sim L C C' fn fn'
Proof
  strip_tac >> simp[frame_sim_def] >> rpt strip_tac >>
  drule_all scfg_bypass_initial_aligned >> strip_tac >>
  drule_all scfg_bypass_rooted_observe >> strip_tac >>
  `active_inst fn i u` by metis_tac[frame_reach_active] >>
  drule_all scfg_bypass_image_observations >> strip_tac >>
  qexistsl_tac [`i`, `u`] >> gvs[]
QED

Theorem scfg_bypass_runs_backward:
  !n t r s. scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ s.vs_inst_idx = 0 /\
  scfg_bypass_aligned a b s t /\
  run_blocks n C fn' t = r /\ terminates r ==>
  ?k. frame_result_rel (run_blocks k C fn s) r
Proof
  Induct_on `n` >- simp[Once run_blocks_def, terminates_def] >>
  rpt gen_tac >> strip_tac >>
  `lookup_block t.vs_current_bb fn'.fn_blocks =
   OPTION_MAP (scfg_bypass_block a b) (lookup_block s.vs_current_bb fn.fn_blocks)` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[] >> strip_tac >- gvs[terminates_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `run_block n C (scfg_bypass_block a b bb) t` >> gvs[]
  >- (Cases_on `v.vs_halted` >> gvs[]
      >- metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
      drule_all scfg_bypass_run_block_OK_backward >> strip_tac >>
      `~u.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
      `scfg_bprefix C fn s0 w` by
        metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
      `w.vs_inst_idx = 0` by
        (qpat_assum `run_block _ _ (scfg_bypass_block _ _ _) _ = OK _`
           (mp_then Any assume_tac venomExecPropsTheory.run_block_OK_inst_idx_0) >>
         gvs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
      `?k. frame_result_rel (run_blocks k C fn w) (run_blocks n C fn' v)` by
        (first_x_assum irule >> simp[]) >>
      `!e. run_blocks k C fn w <> Error e` by
        (drule frame_result_rel_terminates >>
         Cases_on `run_blocks k C fn w` >> simp[terminates_def]) >>
      `?m. run_blocks m C fn u = run_blocks k C fn w` by
        metis_tac[scfg_bprefix_continue] >>
      `?j. run_blocks j C fn s = run_blocks k C fn w` by
        metis_tac[scfg_bstep_continue] >> metis_tac[]) >>
  drule scfg_bypass_run_block_terminal_backward >>
  disch_then (drule_at (Pat `run_block _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `scfg_result q _` >>
  `terminates q /\ (!u. q <> OK u)` by
    (Cases_on `q` >> gvs[scfg_result_def, terminates_def]) >>
  `?m. run_blocks m C fn s = q` by
    (irule scfg_run_block_terminal >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rename1 `run_blocks j C fn s = q` >>
  qexists_tac `j` >> simp[] >> irule scfg_result_terminal >> simp[]
QED

Theorem scfg_bypass_runs_forward:
  !n s r t. scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ s.vs_inst_idx = 0 /\
  scfg_bypass_aligned a b s t /\
  run_blocks n C fn s = r /\ terminates r ==>
  ?k. frame_result_rel r (run_blocks k C fn' t)
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  namedCases_on `n` ["", "n0"] >- gvs[Once run_blocks_def, terminates_def] >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[] >> strip_tac >- gvs[terminates_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  Cases_on `run_block n0 C bb s` >> gvs[]
  >- (Cases_on `v.vs_halted` >> gvs[]
      >- metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
      drule_all scfg_bypass_run_block_OK_forward >>
      disch_then (qx_choosel_then [`v1`, `w`] strip_assume_tac) >>
      qpat_assum `scfg_bprefix C fn v w`
        (mp_then Any mp_tac scfg_bprefix_cancel_bounded) >>
      disch_then (qspec_then `n0` mp_tac) >>
      disch_then (qspec_then `run_blocks n0 C fn v` mp_tac) >>
      simp[] >> strip_tac >>
      `scfg_bprefix C fn s0 w` by
        metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
      `w.vs_inst_idx = 0` by
        (qpat_assum `run_block _ _ (scfg_bypass_block _ _ _) _ = OK _`
           (mp_then Any assume_tac venomExecPropsTheory.run_block_OK_inst_idx_0) >>
         gvs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
      `?k. frame_result_rel (run_blocks n0 C fn v) (run_blocks k C fn' v1)` by
        (qpat_assum `run_blocks m C fn w = _`
           (fn th => once_rewrite_tac[GSYM th]) >>
         first_x_assum irule >> simp[] >> decide_tac) >>
      `!e. run_blocks k C fn' v1 <> Error e` by
        (drule frame_result_rel_terminates >>
         Cases_on `run_blocks k C fn' v1` >> simp[terminates_def]) >>
      `?j. run_blocks j C fn' t = run_blocks k C fn' v1` by
        metis_tac[scfg_bstep_continue, venomExecPropsTheory.run_block_OK_not_halted] >>
      metis_tac[]) >>
  drule scfg_bypass_run_block_terminal_forward >>
  disch_then (drule_at (Pat `run_block _ _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `scfg_result _ q` >>
  `terminates q /\ (!u. q <> OK u)` by
    (Cases_on `q` >> gvs[scfg_result_def, terminates_def]) >>
  `?j. run_blocks j C fn' t = q` by
    (irule scfg_run_block_terminal >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `j` >> simp[] >> irule scfg_result_terminal >> simp[]
QED

Theorem scfg_bypass_runs_forward_fuel_from_terminal:
  (!s bb t k r.
    scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
    scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
    run_block k C bb s = r /\ terminates r /\ (!v. r <> OK v) ==>
    ?q. run_block k C (scfg_bypass_block a b bb) t = q /\ scfg_result r q) ==>
  !n s r t. scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ s.vs_inst_idx = 0 /\
  scfg_bypass_aligned a b s t /\
  run_blocks n C fn s = r /\ terminates r ==>
  frame_result_rel r (run_blocks n C fn' t)
Proof
  disch_then (mk_asm "terminal") >>
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  namedCases_on `n` ["", "n0"] >- gvs[Once run_blocks_def, terminates_def] >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[] >> strip_tac >- gvs[terminates_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  Cases_on `run_block n0 C bb s` >> gvs[]
  >- suspend "continue_fuel" >>
  gvs[terminates_def] >>
  `?q. run_block n0 C (scfg_bypass_block a b bb) t = q /\
       scfg_result (run_block n0 C bb s) q` by
    (asm "terminal" irule >> simp[terminates_def] >>
     qexists_tac `s` >> simp[]) >>
  Cases_on `q` >> gvs[scfg_result_def] >>
  irule scfg_result_terminal >> simp[scfg_result_def, terminates_def]
QED

Resume scfg_bypass_runs_forward_fuel_from_terminal[continue_fuel]:
  Cases_on `v.vs_halted` >> gvs[]
  >- metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  drule_all scfg_bypass_run_block_OK_forward >>
  disch_then (qx_choosel_then [`v1`, `w`] strip_assume_tac) >>
  qpat_assum `scfg_bprefix C fn v w`
    (mp_then Any mp_tac scfg_bprefix_cancel_bounded) >>
  disch_then (qspec_then `n0` mp_tac) >>
  disch_then (qspec_then `run_blocks n0 C fn v` mp_tac) >>
  simp[] >> strip_tac >>
  `scfg_bprefix C fn s0 w` by
    metis_tac[scfg_bprefix_single, scfg_bprefix_trans] >>
  `w.vs_inst_idx = 0` by
    (qpat_assum `run_block _ _ (scfg_bypass_block _ _ _) _ = OK _`
       (mp_then Any assume_tac venomExecPropsTheory.run_block_OK_inst_idx_0) >>
     gvs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  `frame_result_rel (run_blocks n0 C fn v) (run_blocks m C fn' v1)` by
    (qpat_assum `run_blocks m C fn w = _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  `run_blocks n0 C fn' v1 = run_blocks m C fn' v1` by
    (irule run_blocks_terminates_mono >> simp[] >>
     metis_tac[frame_result_rel_terminates]) >>
  `~v1.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  once_rewrite_tac[run_blocks_unfold] >> simp[]
QED

Finalise scfg_bypass_runs_forward_fuel_from_terminal

Theorem scfg_bypass_fn_bisim:
  scfg_bypass_hyp fn a b fn' ==> fn_bisim fn fn'
Proof
  strip_tac >> rewrite_tac[fn_bisim_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[scfg_bypass_entry_eq] >>
  conj_tac >- (fs[scfg_bypass_hyp_def] >> drule do_merge_jump_metadata >> simp[fn_identity_metadata_eq_def]) >>
  conj_tac >- simp[] >> rpt strip_tac >>
  `scfg_bypass_aligned a b s s` by metis_tac[scfg_bypass_initial_aligned] >>
  `scfg_bprefix ctx fn s s /\ s.vs_inst_idx = 0` by
    fs[scfg_bprefix_rules, fn_entry_state_def] >>
  FIRST [irule scfg_bypass_runs_forward, irule scfg_bypass_runs_backward] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem scfg_bypass_fn_bisim_fuel:
  scfg_bypass_hyp fn a b fn' ==> fn_bisim_fuel I fn fn'
Proof
  strip_tac >> rewrite_tac[fn_bisim_fuel_def] >>
  `fn_entry_label fn' = fn_entry_label fn` by metis_tac[scfg_bypass_entry_eq] >>
  conj_tac >- (fs[scfg_bypass_hyp_def] >> drule do_merge_jump_metadata >>
              simp[fn_identity_metadata_eq_def]) >>
  conj_tac >- simp[] >> rpt strip_tac >> simp[] >>
  `scfg_bypass_aligned a b s s` by metis_tac[scfg_bypass_initial_aligned] >>
  `scfg_bprefix ctx fn s s /\ s.vs_inst_idx = 0` by
    fs[scfg_bprefix_rules, fn_entry_state_def] >>
  irule scfg_bypass_runs_forward_fuel_from_terminal >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[scfg_bypass_run_block_terminal_forward_fuel]
QED
