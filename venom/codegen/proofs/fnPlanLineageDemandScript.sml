Theory fnPlanLineageDemand
Ancestors
  livenessProofs cfgAnalysisProps venomWf list rich_list

Theorem live_prefix_demand:
  !fn lbl bb n v.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    n <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) lbl n) ==>
    MEM v (live_vars_at (liveness_analyze fn) lbl 0) \/
    MEM v (FLAT (MAP inst_defs (TAKE n bb.bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM v (FLAT (MAP inst_defs (TAKE n bb.bb_instructions)))`
  >- simp[] >>
  disj1_tac >>
  drule live_vars_at_propagate_range >> simp[] >>
  disch_then irule >> simp[] >>
  qexists_tac `n` >> simp[] >>
  rpt strip_tac >>
  `MEM (EL k bb.bb_instructions) (TAKE n bb.bb_instructions)` by
    (simp[MEM_EL] >> qexists_tac `k` >> simp[EL_TAKE]) >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED
