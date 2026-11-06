Theory fnLineageInvPointLive
Ancestors fnPlanLineagePath fnPlanLineagePhiActivation livenessAnalysisProps
  venomWf venomInst venomExecProps codegenReadyCompute list rich_list pred_set
  stackPlanGen cfgAnalysisProps

val _ = print (thm_to_string listTheory.LRC_MEM_right ^ "\n");

Theorem analyzed_output_live_point_to_after:
  !fn d bb j v p pb k.
    codegen_ready_fn fn /\ lookup_block d fn.fn_blocks = SOME bb /\
    j < LENGTH bb.bb_instructions /\ MEM v (EL j bb.bb_instructions).inst_outputs /\
    fn_dominates fn d p /\ lookup_block p fn.fn_blocks = SOME pb /\
    LENGTH (collect_phis pb.bb_instructions) <= k /\ k <= LENGTH pb.bb_instructions /\
    (d = p ==> j < k) /\
    MEM v (live_vars_at (liveness_analyze fn) p k) ==>
    MEM v (live_vars_at (liveness_analyze fn) d (j+1))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  drule_all dominates_analyzed_path_no_revisit >> strip_tac >>
  `MEM d (cfg_analyze fn).cfg_dfs_pre` by gvs[] >>
  Cases_on `d = p`
  >- (gvs[] >>
      drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
      disch_then (qspecl_then [`d`, `bb`, `j+1`, `k`, `v`] mp_tac) >>
      simp[] >> disch_then irule >> simp[] >>
      rpt strip_tac >> gvs[inst_defs_def] >>
      `j < LENGTH bb.bb_instructions /\ k' < LENGTH bb.bb_instructions` by decide_tac >>
      `k' = j` by metis_tac[ssa_output_position_unique] >> decide_tac) >>
  suspend "different_blocks"
QED

Resume analyzed_output_live_point_to_after[different_blocks]:
  `tail <> []` by (Cases_on `tail` >> gvs[]) >>
  `?pre. tail = pre ++ [p]` by
    (qexists_tac `FRONT tail` >>
     `LAST tail = p` by (Cases_on `tail` >> gvs[]) >>
     metis_tac[APPEND_FRONT_LAST]) >>
  gvs[] >>
  drule_at Any codegenReadyComputeTheory.is_fn_path_to_lrc >> simp[] >>
  strip_tac >>
  FAIL_TAC "split lrc"
QED

Finalise analyzed_output_live_point_to_after
