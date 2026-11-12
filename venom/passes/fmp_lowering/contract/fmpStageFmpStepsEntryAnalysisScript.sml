Theory fmpStageFmpStepsEntryAnalysis
Ancestors
  fmpStageRel fmpStageReclaimFresh fmpReclaimProps fmpLowerDefs
  fmpReclaimDefs venomInst

Theorem fmp_stage_root_analyses:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (lbl,rp) ==>
  ?env states.
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states
Proof
  strip_tac >>
  `fn.fn_fmp_signature = NONE` by
    (gvs[fmp_stage_root_def, AllCaseEqs()]) >>
  qpat_x_assum `fmp_stage_lowered _ _ _ _ _` mp_tac >>
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def] >>
  Cases_on `analyze_fmp_reclaims infos ctx fn` >>
  simp[AllCaseEqs()] >> strip_tac >>
  gvs[analyze_fmp_reclaims_def, AllCaseEqs()] >>
  metis_tac[fmp_reclaim_states_has_bases]
QED

Theorem fmp_stage_entry_analysis:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (lbl,0) /\
  wf_function fn /\ fn_entry_label fn = SOME lbl ==>
  ?env states st.
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states lbl 0 = SOME st /\ st.frs_stack = []
Proof
  strip_tac >> drule_all fmp_stage_root_analyses >> strip_tac >>
  qpat_x_assum `fn_entry_label _ = _` mp_tac >>
  simp[fn_entry_label_def] >>
  Cases_on `entry_block fn` >> simp[] >> strip_tac >>
  drule_all reclaim_fresh_entry >> strip_tac >> metis_tac[]
QED
