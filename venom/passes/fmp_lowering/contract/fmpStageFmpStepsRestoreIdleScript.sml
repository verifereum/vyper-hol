Theory fmpStageFmpStepsRestoreIdle
Ancestors
  fmpStageRel fmpStageControl fmpStageFmpStepsLedgerRestrict
  fmpLowerReclaimPlan fmpLowerDefs fmpReclaimDefs venomExecProps
  finite_map list pair

Theorem fmp_restore_idle_plan:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states infos fn = SOME states ==>
  fmp_stage_plan infos ctx fn = fmp_candidate_plan infos ctx fn states
Proof
  simp[fmp_stage_lowered_def] >> strip_tac >>
  qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = _` mp_tac >>
  simp[fmp_lower_function_with_info_def] >>
  Cases_on `analyze_fmp_reclaims infos ctx fn` >>
  simp[] >> strip_tac >>
  gvs[fmp_stage_plan_def, analyze_fmp_reclaims_def, AllCaseEqs()]
QED

Theorem fmp_restore_idle_pop:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  df_at NONE states bb.bb_label k = SOME st /\
  ~((bb.bb_label,k) IN FDOM (fmp_stage_plan infos ctx fn)) ==>
  SND (fmp_pop_at infos fn (liveness_analyze fn) env (bb.bb_label,k)
         (EL k bb.bb_instructions) st) = st.frs_stack
Proof
  strip_tac >> drule_all fmp_restore_idle_plan >> strip_tac >>
  drule_all fmp_candidate_plan_lookup >>
  disch_then (qspecl_then [`states`, `infos`, `ctx`] assume_tac) >>
  Cases_on `fmp_pop_at infos fn (liveness_analyze fn) env (bb.bb_label,k)
    (EL k bb.bb_instructions) st` >>
  rename1 `_ = (popped,kept)` >>
  `fmp_pop_target popped = NONE` by
    (gvs[fmp_reclaim_step_def, FLOOKUP_DEF]) >>
  drule_all fmp_pop_at_none >> simp[]
QED

Theorem fmp_restore_idle_empty:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  df_at NONE states bb.bb_label k = SOME st /\ st.frs_stack = [] ==>
  ~((bb.bb_label,k) IN FDOM (fmp_stage_plan infos ctx fn))
Proof
  strip_tac >> drule_all fmp_restore_idle_plan >> strip_tac >>
  drule_all fmp_candidate_plan_lookup >>
  disch_then (qspecl_then [`states`, `infos`, `ctx`] assume_tac) >>
  gvs[fmp_reclaim_step_def, fmp_pop_at_def, fmp_pop_prefix_def,
      fmp_pop_target_def, FLOOKUP_DEF] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* An explicit witness constructor: callers unpack the old frame once and
   pass that same infos/ctx/runner here, so no plan-witness ambiguity arises. *)
Theorem fmp_restore_idle_frame:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\
  ~((s.vs_current_bb,s.vs_inst_idx) IN
       FDOM (fmp_stage_plan infos ctx fn)) /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions s.vs_inst_idx /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb s.vs_inst_idx) G tv s t /\ fmp_params_rel sm PG s t /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\ s.vs_data_section = t.vs_data_section /\
  s.vs_labels = t.vs_labels /\ s.vs_code = t.vs_code /\
  s.vs_prev_hashes = t.vs_prev_hashes /\
  w2n s.vs_initial_fmp = raw0 /\ w2n t.vs_initial_fmp = fmp0 /\
  fmp_frontier_rel fmp0 raw0 lo s.vs_fmp /\ elo <= lo /\ eb <= w2n s.vs_fmp /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
    (eb <= b <=> elo <= c) /\ (b < eb ==> c + z <= elo /\ b + z <= eb)) /\
  (case fmp_stage_root infos ctx fn of NONE => lo = elo
   | SOME (rl,rp) => ?env states st.
     fmp_base_analyze (fn_insts fn) = SOME env /\
     fmp_reclaim_states infos fn = SOME states /\
     df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
     fmp_frame_covers sm env eb lo G /\
     (if s.vs_current_bb = rl /\ s.vs_inst_idx < rp then
        lo = elo /\ st.frs_stack = [] /\
        (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
        (~fn_is_context_entry ctx fn ==>
          LENGTH s.vs_params = LENGTH (fn_user_param_insts fn) /\
          LENGTH s.vs_params < LENGTH t.vs_params /\
          EL (LENGTH s.vs_params) t.vs_params = n2w elo)
      else lookup_var runner t = SOME (n2w lo) /\
        ?regions. fmp_ledger_ok (fn_insts fn) env t lo regions /\
          MAP (\r. r.fr_mark) regions = st.frs_stack /\
          EVERY (\r. elo <= r.fr_lo) regions /\
          fmp_ledger_link sm eb lo regions)) ==>
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tv s t
Proof
  strip_tac >> simp[fmp_frame_rel_def] >>
  qexistsl [`infos`, `ctx`, `runner`] >> gvs[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >- gvs[] >>
  rename1 `_ = SOME root` >> PairCases_on `root` >> gvs[] >>
  `fn.fn_fmp_signature = NONE` by
    (qpat_x_assum `fmp_stage_root _ _ _ = _` mp_tac >>
     simp[fmp_stage_root_def] >> rw[] >> gvs[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    (drule venomExecProofsTheory.lookup_block_MEM >> strip_tac >>
     drule venomExecProofsTheory.lookup_block_label >> simp[]) >>
  `SND (fmp_pop_at infos fn (liveness_analyze fn) env
     (s.vs_current_bb,s.vs_inst_idx) (EL s.vs_inst_idx bb.bb_instructions) st)
     = st.frs_stack` by
    (qpat_assum `bb.bb_label = _` (fn th => rewrite_tac[GSYM th]) >>
     irule fmp_restore_idle_pop >> metis_tac[]) >>
  Cases_on `t.vs_current_bb = root0 /\ s.vs_inst_idx < root1` >- gvs[] >>
  Cases_on `t.vs_current_bb = root0` >> gvs[] >>
  qexists `regions` >> simp[]
QED
