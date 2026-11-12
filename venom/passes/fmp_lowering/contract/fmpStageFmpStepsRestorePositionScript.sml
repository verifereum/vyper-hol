Theory fmpStageFmpStepsRestorePosition
Ancestors
  fmpStageRel fmpStageControl fmpStageControlLayout fmpStepReclaim
  fmpStageFmpStepsRestoreIdle fmpAnalysisProps fmpLowerProps fmpLowerDefs
  fmpAnalysisDefs fmpReclaimDefs fmpStepLayout finite_map list venomInst

Theorem fmp_restore_dalloca_needs[local]:
  MEM inst insts /\ inst.inst_opcode = DALLOCA ==>
  (fmp_scan_insts insts).fi_needs_fmp
Proof
  Induct_on `insts` >> simp[fmp_scan_insts_def, fmp_info_bottom_def,
    fmp_info_join_def] >> rpt strip_tac >> gvs[fmp_opcode_needs_fmp_def] >>
  metis_tac[]
QED

Theorem fmp_restore_planned_needs:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  point IN FDOM (fmp_stage_plan infos ctx fn) ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info /\ info.fi_needs_fmp
Proof
  strip_tac >>
  `?plan target. analyze_fmp_reclaims infos ctx fn = SOME plan /\
    fmp_stage_plan infos ctx fn = plan /\ FLOOKUP plan point = SOME target` by
    (Cases_on `analyze_fmp_reclaims infos ctx fn` >>
     gvs[fmp_stage_plan_def, FLOOKUP_DEF]) >>
  drule_all analyze_fmp_reclaims_output >> strip_tac >>
  `(fmp_direct_info fn).fi_needs_fmp` by
    (simp[fmp_direct_info_def] >> metis_tac[fmp_restore_dalloca_needs]) >>
  fs[fmp_stage_lowered_def] >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs()] >>
  `MEM fn ctx.ctx_functions` by
    (gvs[fmp_lower_input_def] >> metis_tac[lookup_function_MEM]) >>
  drule_all analyze_fmp_context_unsealed_direct_fields >> simp[]
QED

Theorem fmp_restore_planned_position:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) ==>
  ?rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
          ~(lbl = rl /\ idx < rp)
Proof
  strip_tac >> drule_all fmp_restore_planned_needs >> strip_tac >>
  drule fmp_control_rewrite >> disch_then (qspec_then `info` mp_tac) >>
  simp[] >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  drule_all fmp_control_root_layout >> strip_tac >>
  `root <> NONE` by metis_tac[] >>
  qexistsl [`entry.bb_label`, `LENGTH users + LENGTH (OPTION_TO_LIST oldpc)`] >>
  conj_tac >- gvs[] >>
  rpt strip_tac >> drule_all fmp_control_prefix_plan_absent >>
  gvs[FLOOKUP_DEF]
QED

Theorem fmp_restore_planned_target:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  df_at NONE states bb.bb_label k = SOME st /\
  FLOOKUP (fmp_stage_plan infos ctx fn) (bb.bb_label,k) = SOME target ==>
  fmp_pop_target (FST (fmp_pop_at infos fn (liveness_analyze fn) env
    (bb.bb_label,k) (EL k bb.bb_instructions) st)) = SOME target
Proof
  strip_tac >> drule_all fmp_restore_idle_plan >> strip_tac >>
  drule_all fmpLowerReclaimPlanTheory.fmp_candidate_plan_lookup >>
  disch_then (qspecl_then [`states`, `infos`, `ctx`] assume_tac) >>
  Cases_on `fmp_pop_at infos fn (liveness_analyze fn) env (bb.bb_label,k)
    (EL k bb.bb_instructions) st` >> gvs[fmp_reclaim_step_def]
QED
