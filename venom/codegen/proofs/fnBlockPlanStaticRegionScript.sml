Theory fnBlockPlanStaticRegion
Ancestors
  fnBlockPlanStaticPromises fnBlockPlanStaticInventory fnPlanLineage

Theorem dfs_saved_parent_origin_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg /\
    ?lbl rest seen pin bb bops pout.
      dfs_aux_call lv dfg cfg fn ps0 (lbl::rest) seen pin /\
      ~MEM lbl seen /\ lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
      ss = pout.ps_stack /\ sp = pout.ps_spilled /\
      (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl)))
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- metis_tac[dfs_aux_call_entry]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_missing]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_succs]
      >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- metis_tac[dfs_aux_call_rest]
  >- (rpt strip_tac >> irule dfs_aux_call_branch >>
      goal_assum (drule_at Any) >> simp[])
  >> rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[dfs_aux_call_sibling]
  >> metis_tac[listTheory.MEM]
QED

Theorem dfs_saved_parent_origin:
  dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
  ?lbl rest seen pin bb bops pout.
    dfs_aux_call lv dfg cfg fn ps0 (lbl::rest) seen pin /\
    ~MEM lbl seen /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
    ss = pout.ps_stack /\ sp = pout.ps_spilled /\
    (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl))
Proof
  metis_tac[dfs_saved_parent_origin_mutual]
QED

Theorem dfs_saved_parent_block_origin:
  dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
  ?lbl pin bb bops pout.
    dfs_block_state lv dfg cfg fn ps0 lbl pin /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
    ss = pout.ps_stack /\ sp = pout.ps_spilled /\
    (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl))
Proof
  strip_tac >> drule dfs_saved_parent_origin >>
  simp[dfs_block_state_def] >> metis_tac[]
QED
