Theory fnLineageInvSpillReplay
Ancestors planSpillBounds doSwapSim fnLineageInvSupport fnPlanLineage

(* Resource transport only: reachability must separately supply the
   occupied-address inclusion and the replacement map's injectivity. *)
Theorem plan_slots_bounded_occupied_addresses:
  !base q m.
    plan_slots_bounded base q /\
    (!op off. FLOOKUP m op = SOME off ==>
       ?old. FLOOKUP q.ps_spilled old = SOME off) ==>
    plan_slots_bounded base (q with ps_spilled := m)
Proof
  rw[plan_slots_bounded_def] >> metis_tac[]
QED

Theorem spill_alloc_layout_wf_occupied_addresses:
  !al old m.
    spill_alloc_layout_wf al old /\
    (!op off. FLOOKUP m op = SOME off ==>
       ?old_op. FLOOKUP old old_op = SOME off) /\
    (!op1 op2 off. FLOOKUP m op1 = SOME off /\
       FLOOKUP m op2 = SOME off ==> op1 = op2) ==>
    spill_alloc_layout_wf al m
Proof
  rw[spill_alloc_layout_wf_def] >> metis_tac[]
QED

Theorem empty_spill_replacement_resources:
  !base D.
    plan_slots_bounded base D /\
    spill_alloc_layout_wf D.ps_alloc D.ps_spilled ==>
    plan_slots_bounded base (D with ps_spilled := FEMPTY) /\
    spill_alloc_layout_wf D.ps_alloc FEMPTY
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule plan_slots_bounded_occupied_addresses >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule spill_alloc_layout_wf_occupied_addresses >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem analyzed_join_lineage_entry_resources:
  !fn pred succ pb sb dfg ps0 ps base.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block succ fn.fn_blocks = SOME sb /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
    lineage_entry (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 pred succ ps /\
    (!D. dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 succ D ==>
      plan_slots_bounded base D /\ spill_alloc_layout_wf D.ps_alloc D.ps_spilled) ==>
    plan_slots_bounded base ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled
Proof
  rpt gen_tac >> simp[lineage_entry_def] >> rpt strip_tac >> gvs[] >>
  drule_all analyzed_join_edge_block_spills_empty >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule_all empty_spill_replacement_resources >> simp[]
QED
