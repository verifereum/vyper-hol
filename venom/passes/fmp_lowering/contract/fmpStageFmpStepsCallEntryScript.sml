Theory fmpStageFmpStepsCallEntry
Ancestors
  fmpStageRunnerFacts fmpStageRel fmpStageReclaimFresh fmpStepLayout fmpStepStructural
  fmpStageControl fmpLowerDefs fmpReclaimDefs fmpLowerReclaimPlan
  finite_map list words venomExecProofs venomExecSemantics contextCodegenRel
  o1PassContract venomInst

Theorem fmp_call_entry_sites:
  fmp_sites_ok sm fmp0 raw0 lo raw ==>
  !b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
    (w2n raw <= b <=> lo <= c) /\
    (b < w2n raw ==> c + z <= lo /\ b + z <= w2n raw)
Proof
  simp[fmp_sites_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!b z c id. _ ==> 0 < z /\ _` drule >>
  strip_tac >> decide_tac
QED

Theorem fmp_call_pending_root:
  fmp_stage_lowered infos ctx runner fn fn' /\
  ~fn_is_context_entry ctx fn /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
  ?users pc tail bb rest plan states env.
    split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) /\
    fn.fn_blocks = bb::rest /\ rl = bb.bb_label /\ rp = SUC (LENGTH users) /\
    analyze_fmp_reclaims infos ctx fn = SOME plan /\
    fmp_reclaim_states infos fn = SOME states /\
    fmp_base_analyze (fn_insts fn) = SOME env
Proof
  simp[fmp_stage_root_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[fmp_stage_lowered_def, fmp_lower_function_with_info_def,
      AllCaseEqs()] >>
  imp_res_tac fmpLowerReclaimPlanTheory.analyze_fmp_reclaims_candidate >>
  gvs[fmp_reclaim_states_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_call_setup_entry:
  first_block_no_phi fn /\ setup_callee fn args s = SOME cs ==>
  (enters_block fn cs s1 <=> s1 = cs) /\
  cs.vs_vars = FEMPTY /\ cs.vs_params = args /\
  cs.vs_inst_idx = 0 /\ cs.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME cs.vs_current_bb
Proof
  Cases_on `fn.fn_blocks` >>
  simp[setup_callee_def, first_block_no_phi_def] >> rpt strip_tac >> gvs[] >>
  simp[enters_block_def, lookup_block_def, FIND_thm,
       eval_phis_no_phis, no_phis_phi_prefix_length_zero,
       fn_entry_label_def, entry_block_def]
QED

Theorem fmp_call_initial_analysis:
  fmp_stage_lowered infos ctx runner fn fn' /\ wf_function fn /\
  ~fn_is_context_entry ctx fn /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
  0 < rp /\ fn_entry_label fn = SOME rl /\
  ?env states st.
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states rl 0 = SOME st /\ st.frs_stack = []
Proof
  strip_tac >> drule_all fmp_call_pending_root >> strip_tac >> gvs[] >>
  `entry_block fn = SOME bb` by simp[entry_block_def] >>
  drule_all reclaim_fresh_entry >> strip_tac >>
  simp[fn_entry_label_def, entry_block_def] >> metis_tac[]
QED

Theorem fmp_call_frame_entry:
  fmp_frame_rel sm fmp0 raw0 eb elo lo restored caller caller' Q H tv s t /\
  fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  wf_function fn /\ first_block_no_phi fn /\ ~fn_is_context_entry ctx fn /\
  setup_callee fn args s = SOME cs /\ setup_callee fn' argst t = SOME ct /\
  enters_block fn cs s1 /\ enters_block fn' ct t1 /\
  fmp_params_rel sm PG cs ct /\
  LENGTH args = LENGTH (fn_user_param_insts fn) /\
  (!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
     LENGTH args < LENGTH argst /\ EL (LENGTH args) argst = n2w lo) ==>
  fmp_frame_rel sm fmp0 raw0 (w2n s.vs_fmp) lo lo F
    fn fn' PG FEMPTY FEMPTY s1 t1
Proof
  strip_tac >>
  drule_all fmp_stage_lowered_shape >> strip_tac >>
  qpat_x_assum `first_block_no_phi _ ==> _` drule >> strip_tac >>
  `s1 = cs /\ cs.vs_vars = FEMPTY /\ cs.vs_inst_idx = 0 /\
   cs.vs_prev_bb = NONE /\ fn_entry_label fn = SOME cs.vs_current_bb` by
    metis_tac[fmp_call_setup_entry] >>
  `t1 = ct /\ ct.vs_vars = FEMPTY /\ ct.vs_inst_idx = 0 /\
   ct.vs_prev_bb = NONE /\ fn_entry_label fn' = SOME ct.vs_current_bb` by
    metis_tac[fmp_call_setup_entry] >> gvs[] >>
  `cs.vs_current_bb = ct.vs_current_bb` by metis_tac[] >>
  drule fmp_call_entry_sites >> strip_tac >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once fmp_frame_rel_def] >> strip_tac >>
  pure_rewrite_tac[fmp_frame_rel_def, LET_THM] >>
  qexistsl [`infos`, `ctx`, `runner`] >>
  gvs[setup_callee_def] >>
  simp[fmp_env_rel_def, fmp_frame_covers_def] >>
  Cases_on `fmp_stage_root infos ctx fn`
  >- (simp[fmp_stage_tidx_def] >> rpt strip_tac >>
      qpat_x_assum `!b z c id. _ ==> (w2n s.vs_fmp <= b <=> _) /\ _`
        drule >> simp[]) >>
  rename1 `fmp_stage_root infos ctx fn = SOME rr` >> PairCases_on `rr` >>
  drule_all fmp_call_initial_analysis >> strip_tac >> gvs[] >>
  simp[fmp_stage_tidx_def, fmp_frame_covers_def] >>
  metis_tac[]
QED
