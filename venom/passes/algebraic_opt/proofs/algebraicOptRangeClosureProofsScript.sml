Theory algebraicOptRangeClosureProofs
Ancestors
  assertElimProofs algebraicOptRangeConditionProofs venomWf venomInst
  rangeAnalysisDefs rangeAnalysisProofs sccpCorrectnessProofs sccpProofsBase
  algebraicOptReachabilityProofs algebraicOptTraceProofs cfgAnalysisProps list
  algebraicOptRangeProofs venomState venomExecSemantics unitShapeDefs

Theorem ao_range_exit_boundary_sound:
  !fn bb s.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    bb.bb_instructions <> [] /\
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label
                   (LENGTH bb.bb_instructions)) s ==>
    ?rs. df_widen_boundary NONE (range_analyze fn) bb.bb_label = SOME rs /\
         in_range_state rs s.vs_vars
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
  `?exit_rs. df_widen_at NONE (range_analyze fn) bb.bb_label
                (LENGTH bb.bb_instructions) = SOME exit_rs` by
    (irule (SIMP_RULE std_ss [LET_THM] range_widen_at_some) >>
     simp[] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule_all (cj 2 (SIMP_RULE std_ss [LET_THM] range_fixpoint_absorbs)) >> simp[] >> strip_tac >>
  Cases_on `df_widen_boundary NONE (range_analyze fn) bb.bb_label`
  >- gvs[range_join_opt_def] >>
  rename1 `df_widen_boundary NONE (range_analyze fn) bb.bb_label = SOME rs` >>
  qexists_tac `rs` >> simp[] >>
  gvs[] >> drule range_join_opt_some_sound_right >>
  disch_then (qspec_then `SOME rs` mp_tac) >>
  gvs[range_sound_def]
QED

Theorem ao_source_prefix_index_bound:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    s0.vs_inst_idx = 0 ==>
    !bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ ~phase ==>
         s.vs_inst_idx <= LENGTH bb.bb_instructions
Proof
  ho_match_mp_tac algebraicOptReachabilityProofsTheory.ao_source_prefix_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac
  >- simp[]
  >- (rpt strip_tac >>
      drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
      strip_tac >> gvs[] >>
      metis_tac[venomExecProofsTheory.phi_prefix_length_le])
  >- (rpt strip_tac >>
      drule_all venomInstPropsTheory.step_preserves_control_flow >>
      strip_tac >> gvs[] >>
      gvs[get_instruction_def, AllCaseEqs()])
  >> simp[]
QED

Theorem ao_terminator_final_position:
  !fn bb idx inst.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    get_instruction bb idx = SOME inst /\ is_terminator inst.inst_opcode ==>
    SUC idx = LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  gvs[get_instruction_def, AllCaseEqs()] >>
  `idx = PRE (LENGTH bb.bb_instructions)` by metis_tac[bb_well_formed_def] >>
  decide_tac
QED

Theorem ao_source_prefix_dfs:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb ==>
    MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  ho_match_mp_tac ao_source_prefix_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- metis_tac[entry_label_in_dfs_pre]
  >- (drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
      strip_tac >> gvs[])
  >- (drule_all venomInstPropsTheory.step_preserves_control_flow >>
      strip_tac >> gvs[])
  >> rename1 `step_inst k ctx inst s = OK t` >>
  `ao_source_step ctx fn (k,F,s) (k,T,t)` by
       (simp[Once ao_source_step_cases] >> metis_tac[]) >>
  drule_all ao_source_step_exit_cfg >> strip_tac >>
  metis_tac[fn_cfg_edge_in_dfs_pre]
QED

Theorem ao_source_prefix_block:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s /\
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb ==>
    ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >> drule_all ao_source_prefix_dfs >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) s.vs_current_bb` by
    (drule cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all cfg_analyze_reachable_in_labels >>
  simp[fn_labels_def, MEM_MAP] >> strip_tac >>
  rename1 `MEM bb fn.fn_blocks` >>
  qexists_tac `bb` >> irule venomExecPropsTheory.MEM_lookup_block >>
  gvs[wf_function_def, fn_labels_def]
QED

Theorem ao_source_prefix_edge_cfg:
  !ctx fn s0 n k s t.
    ao_source_prefix ctx fn s0 n k F s /\
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME s0.vs_current_bb /\
    ao_source_step ctx fn (k,F,s) (k,T,t) ==>
    MEM t.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    MEM s.vs_current_bb (cfg_preds_of (cfg_analyze fn) t.vs_current_bb) /\
    ?bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb
Proof
  rpt gen_tac >> strip_tac >>
  `ao_source_prefix ctx fn s0 n k T t` by
    (drule ao_source_step_prefix >> simp[] >>
     disch_then drule >> simp[]) >>
  conj_tac >- metis_tac[ao_source_prefix_dfs] >>
  conj_tac
  >- (drule_all ao_source_step_exit_cfg >>
      simp[fn_cfg_edge_def] >> strip_tac >>
      simp[GSYM cfg_edge_symmetry_uncond] >>
      gvs[wf_function_def] >> drule_all bb_succs_in_cfg_succs >> simp[]) >>
  metis_tac[ao_source_prefix_block]
QED

Theorem range_refined_boundary_entry_sound:
  !fn pred succ rs s.
    wf_function fn /\
    MEM succ (cfg_analyze fn).cfg_dfs_pre /\
    MEM pred (cfg_preds_of (cfg_analyze fn) succ) /\
    df_widen_boundary NONE (range_analyze fn) pred = SOME rs /\
    in_range_state
      (range_branch_refine (dfg_build_function fn) fn.fn_blocks pred succ rs)
      s.vs_vars ==>
    range_sound (df_widen_entry NONE (range_analyze fn) succ) s
Proof
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `range_sound entry s` >>
  qabbrev_tac `edges = MAP (\nbr. range_edge_transfer_opt
    (dfg_build_function fn, fn.fn_blocks) nbr succ
    (df_widen_boundary NONE (range_analyze fn) nbr))
    (cfg_preds_of (cfg_analyze fn) succ)` >>
  `MEM (SOME (range_branch_refine (dfg_build_function fn)
    fn.fn_blocks pred succ rs)) edges` by
    (simp[Abbr `edges`, MEM_MAP] >> qexists `pred` >>
     simp[range_edge_transfer_opt_some]) >>
  `edges <> []` by (strip_tac >> gvs[]) >>
  drule_all range_fixpoint_absorbs >>
  simp_tac std_ss [LET_THM] >>
  qpat_assum `Abbrev (edges = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `Abbrev (entry = _)`
    (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  Cases_on `edges` >- fs[] >> simp[] >> strip_tac >>
  Cases_on `entry = NONE` >- simp[range_sound_def] >>
  Cases_on `entry = SOME FEMPTY` >- simp[range_sound_def, rangeEvalDefsTheory.in_range_state_def] >>
  `entry = FOLDL range_join_opt NONE (h::t)` by
    (Cases_on `df_widen_visits (range_analyze fn) succ >= WIDEN_THRESHOLD` >>
     gvs[] >> metis_tac[range_widen_opt_fixpoint_cases]) >>
  qpat_x_assum `entry = FOLDL _ _ _` SUBST1_TAC >>
  irule foldl_range_join_opt_sound >> metis_tac[]
QED

Theorem ao_source_prefix_range_sound:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
    fn_entry_label fn = SOME s0.vs_current_bb /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
       lookup_var x s0 = NONE) ==>
    in_range_state (range_at_inst (range_analyze fn) s.vs_current_bb
                      (if phase then 0 else s.vs_inst_idx)) s.vs_vars
Proof
  ho_match_mp_tac ao_source_prefix_strongind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- (simp[] >> irule ao_range_at_inst_initial_sound >> metis_tac[])
  >- suspend "phis"
  >- suspend "ordinary"
  >> suspend "edge"
QED
Resume ao_source_prefix_range_sound[phis]:
  `bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[ao_source_prefix_dfs] >>
  drule venomExecProofsTheory.eval_phis_preserves_current_bb >> strip_tac >>
  `in_range_state (range_at_inst (range_analyze fn) s.vs_current_bb 0)
     s.vs_vars` by (fs[] >> metis_tac[]) >>
  drule_at (Pat `eval_phis _ _ = _`) ao_range_phis_sound >> simp[]
QED
Resume ao_source_prefix_range_sound[ordinary]:
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[ao_source_prefix_dfs] >>
  `in_range_state (range_at_inst (range_analyze fn) s.vs_current_bb
      s.vs_inst_idx) s.vs_vars` by (fs[] >> metis_tac[]) >>
  drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
  `SUC s.vs_inst_idx <= LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  simp[] >> irule ao_range_step_sound >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume ao_source_prefix_range_sound[edge]:
  rename1 `step_inst k ctx inst s = OK t` >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[ao_source_prefix_dfs] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
              venomExecPropsTheory.lookup_block_label] >>
  `SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
    metis_tac[ao_terminator_final_position] >>
  `in_range_state (range_at_inst (range_analyze fn) s.vs_current_bb
      s.vs_inst_idx) s.vs_vars` by (fs[] >> metis_tac[]) >>
  `in_range_state (range_at_inst (range_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)) t.vs_vars` by
    (qpat_assum `SUC _ = LENGTH _` (fn th => rewrite_tac[GSYM th]) >>
     irule ao_range_step_sound >>
     goal_assum (drule_at Any) >> gvs[get_instruction_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)) t` by
    (Cases_on `df_widen_at NONE (range_analyze fn) bb.bb_label
       (LENGTH bb.bb_instructions)` >>
     gvs[range_at_inst_def, range_sound_def, range_unwrap_def]) >>
  `bb.bb_instructions <> []` by (strip_tac >> gvs[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by simp[] >>
  drule_all ao_range_exit_boundary_sound >> strip_tac >>
  `t.vs_vars = s.vs_vars` by
    (rw[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM] >>
     drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
     disch_then (qspec_then `x` mp_tac) >> simp[lookup_var_def]) >>
  `ao_source_step ctx fn (k,F,s) (k,T,t)` by
    (simp[Once ao_source_step_cases] >> metis_tac[]) >>
  drule_all ao_source_prefix_edge_cfg >> strip_tac >>
  drule ao_source_prefix_has_trace >> strip_tac >>
  `in_range_state
     (range_branch_refine (dfg_build_function fn) fn.fn_blocks
        s.vs_current_bb t.vs_current_bb rs) t.vs_vars` by
    (irule ao_source_trace_branch_refine_sound >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`ctx`, `k`, `trace`] >> simp[] >> metis_tac[]) >>
  `df_widen_boundary NONE (range_analyze fn) s.vs_current_bb = SOME rs`
    by metis_tac[] >>
  drule_all range_refined_boundary_entry_sound >> strip_tac >>
  drule_all range_entry_eq >> strip_tac >>
  Cases_on `df_widen_entry NONE (range_analyze fn) t.vs_current_bb` >>
  gvs[range_at_inst_def, range_sound_def, range_unwrap_def,
      rangeEvalDefsTheory.in_range_state_def] >> metis_tac[]
QED
Finalise ao_source_prefix_range_sound

Theorem ao_source_prefix_operand_range_sound:
  !ctx fn s0 n k phase s op w.
    ao_source_prefix ctx fn s0 n k phase s /\
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
    fn_entry_label fn = SOME s0.vs_current_bb /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
       lookup_var x s0 = NONE) /\
    eval_operand op s = SOME w ==>
    in_range (range_get_range (range_analyze fn) s.vs_current_bb
                (if phase then 0 else s.vs_inst_idx) op) w
Proof
  rpt strip_tac >> irule ao_range_eval_operand_sound >>
  goal_assum (drule_at Any) >>
  irule ao_source_prefix_range_sound >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
