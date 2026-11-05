Theory algebraicOptRangeClosureProofs
Ancestors
  assertElimProofs algebraicOptRangeConditionProofs venomWf venomInst
  rangeAnalysisDefs rangeAnalysisProofs

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
