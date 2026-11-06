Theory fnLineageInvOwnerOrigin
Ancestors fnPlanLineage stackPlanGen stackPlanTypes list allocMono doSwapSim

Theorem dfs_calls_owner_origin[local]:
  !lv dfg cfg fn ps0.
  (!wl visited ps.
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps /\
    (wl = [] \/
    (?lbl. wl = [lbl] /\
      ((fn_entry_label fn = SOME lbl /\ ps = ps0) \/
       ?pred bb B ops A.
         dfs_block_state lv dfg cfg fn ps0 pred B /\
         lookup_block pred fn.fn_blocks = SOME bb /\
         MEM lbl (cfg_succs_of cfg pred) /\
         generate_block_plan lv dfg cfg fn bb B = SOME (ops,A) /\
         ps.ps_stack = A.ps_stack /\ ps.ps_spilled = A.ps_spilled /\
         ps.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots /\
         ps.ps_alloc.sa_spill_base = A.ps_alloc.sa_spill_base /\
         A.ps_alloc.sa_next_offset <= ps.ps_alloc.sa_next_offset)))) /\
  (!stk spills succs visited ps.
    dfs_succs_call lv dfg cfg fn ps0 stk spills succs visited ps ==>
    dfs_succs_call lv dfg cfg fn ps0 stk spills succs visited ps /\
    (!lbl. MEM lbl succs ==>
      ?pred bb B ops A.
        dfs_block_state lv dfg cfg fn ps0 pred B /\
        lookup_block pred fn.fn_blocks = SOME bb /\
        MEM lbl (cfg_succs_of cfg pred) /\
        generate_block_plan lv dfg cfg fn bb B = SOME (ops,A) /\
        stk = A.ps_stack /\ spills = A.ps_spilled /\
        ps.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots /\
         ps.ps_alloc.sa_spill_base = A.ps_alloc.sa_spill_base /\
         A.ps_alloc.sa_next_offset <= ps.ps_alloc.sa_next_offset))
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >>
  rpt strip_tac >> gvs[] >>
  simp[dfs_aux_call_rules] >>
  simp[dfs_block_state_def]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_succs]
  >- (qexistsl_tac [`lbl`, `bb`, `ps`, `block_ops`, `ps'`] >>
      simp[] >> qexistsl_tac [`[]`, `visited`] >> simp[])
  >- metis_tac[dfs_aux_call_succs]
  >- (qexistsl_tac [`lbl`, `bb`, `ps`, `block_ops`, `ps'`] >>
      simp[] >> qexistsl_tac [`[]`, `visited`] >> simp[])
  >- metis_tac[dfs_aux_call_rest]
  >- metis_tac[dfs_aux_call_rest]
  >- metis_tac[dfs_aux_call_branch]
  >- (irule dfs_aux_call_sibling >> goal_assum (drule_at Any) >> simp[]) >>
  drule (cj 1 fn_plan_aux_alloc_mono) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
  `A.ps_alloc.sa_next_offset <= ps_after.ps_alloc.sa_next_offset` by decide_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[dfs_block_state_def]
QED

Theorem spill_alloc_layout_wf_extension:
  !a b m.
    spill_alloc_layout_wf a m /\
    b.sa_spill_base = a.sa_spill_base /\
    a.sa_next_offset <= b.sa_next_offset /\
    b.sa_free_slots = a.sa_free_slots ==>
    spill_alloc_layout_wf b m
Proof
  simp[spill_alloc_layout_wf_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem dfs_block_state_owner_alloc_origin:
  !lv dfg cfg fn ps0 lbl D.
    dfs_block_state lv dfg cfg fn ps0 lbl D /\
    fn_entry_label fn <> SOME lbl ==>
    ?pred bb B ops A.
      dfs_block_state lv dfg cfg fn ps0 pred B /\
      lookup_block pred fn.fn_blocks = SOME bb /\
      MEM lbl (cfg_succs_of cfg pred) /\
      generate_block_plan lv dfg cfg fn bb B = SOME (ops,A) /\
      D.ps_stack = A.ps_stack /\ D.ps_spilled = A.ps_spilled /\
      D.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots /\
      D.ps_alloc.sa_spill_base = A.ps_alloc.sa_spill_base /\
      A.ps_alloc.sa_next_offset <= D.ps_alloc.sa_next_offset /\
      (spill_alloc_layout_wf A.ps_alloc A.ps_spilled ==>
       spill_alloc_layout_wf D.ps_alloc A.ps_spilled)
Proof
  rpt strip_tac >> gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_owner_origin) >> strip_tac >> gvs[] >>
  `spill_alloc_layout_wf A.ps_alloc A.ps_spilled ==>
   spill_alloc_layout_wf D.ps_alloc A.ps_spilled` by
    (strip_tac >> irule spill_alloc_layout_wf_extension >>
     goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[dfs_block_state_def]
QED

Theorem dfs_block_state_owner_origin:
  !lv dfg cfg fn ps0 lbl D.
    dfs_block_state lv dfg cfg fn ps0 lbl D /\
    fn_entry_label fn <> SOME lbl ==>
    ?pred bb B ops A.
      dfs_block_state lv dfg cfg fn ps0 pred B /\
      lookup_block pred fn.fn_blocks = SOME bb /\
      MEM lbl (cfg_succs_of cfg pred) /\
      generate_block_plan lv dfg cfg fn bb B = SOME (ops,A) /\
      D.ps_stack = A.ps_stack /\ D.ps_spilled = A.ps_spilled /\
      D.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots
Proof
  metis_tac[dfs_block_state_owner_alloc_origin]
QED

Theorem dfs_block_state_unique_predecessor_owner_origin:
  !lv dfg cfg fn ps0 lbl D pred.
    dfs_block_state lv dfg cfg fn ps0 lbl D /\
    fn_entry_label fn <> SOME lbl /\
    (!p. MEM lbl (cfg_succs_of cfg p) ==> p = pred) ==>
    ?bb B ops A.
      dfs_block_state lv dfg cfg fn ps0 pred B /\
      lookup_block pred fn.fn_blocks = SOME bb /\
      MEM lbl (cfg_succs_of cfg pred) /\
      generate_block_plan lv dfg cfg fn bb B = SOME (ops,A) /\
      D.ps_stack = A.ps_stack /\ D.ps_spilled = A.ps_spilled /\
      D.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots
Proof
  rpt strip_tac >> drule_all dfs_block_state_owner_origin >>
  strip_tac >> metis_tac[]
QED
