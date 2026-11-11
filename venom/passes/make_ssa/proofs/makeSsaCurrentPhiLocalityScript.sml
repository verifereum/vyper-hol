Theory makeSsaCurrentPhiLocality
Ancestors
  makeSsaCurrentPlacement makeSsaCurrentDefSupport makeSsaCurrentSelectedLive
  makeSsaCurrentDominanceBridge makeSsaCurrentFrontier
  dominatorDefs venomWf cfgWf list venomInst venomExecProps
  makeSsaCurrentDemandDominance makeSsaCurrentAvailability

Theorem current_selected_live_unique_dominates:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ MEM y (fn_labels fn) /\
  ALOOKUP (select_current_live_in T (liveness_analyze fn) fn) y = SOME vs /\
  MEM v vs /\ MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label y
Proof
  strip_tac >>
  `fn_reachable fn y` by
    (gvs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `?bb. lookup_block y fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP, wf_function_def] >> metis_tac[MEM_lookup_block]) >>
  `current_available fn v y (LENGTH (collect_phis bb.bb_instructions))` by
    (irule current_live_post_phi_available >> simp[current_collect_phis_length] >>
     metis_tac[current_selected_live_phi_cut]) >>
  irule current_semantic_dominates >>
  simp[fn_labels_def, MEM_MAP] >>
  metis_tac[current_available_unique_dominates]
QED

Theorem current_single_live_frontier_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  current_frontier_edge (current_frontier_map fn) db.bb_label y /\
  current_placement_live (select_current_live_in T (liveness_analyze fn) fn) v y ==>
  y = db.bb_label
Proof
  simp[current_frontier_edge_def, current_placement_live_def] >> strip_tac >>
  `MEM db.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  drule_all current_frontier_target_support >> strip_tac >>
  drule_all current_frontier_elim >> strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label y` by
    metis_tac[current_selected_live_unique_dominates] >>
  gvs[strict_dominates_def]
QED

Theorem current_single_pruned_reach_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  (!d. MEM d roots ==> d = db.bb_label) ==>
  !y. current_pruned_reach (current_frontier_map fn)
    (select_current_live_in T (liveness_analyze fn) fn) v roots y ==>
    y = db.bb_label
Proof
  strip_tac >> ho_match_mp_tac current_pruned_reach_ind >> rpt strip_tac
  >- ( `d = db.bb_label` by metis_tac[] >> gvs[] >>
       metis_tac[current_single_live_frontier_local]) >>
  gvs[] >> metis_tac[current_single_live_frontier_local]
QED

Theorem current_compute_defs_pruned_reach_local:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME entry /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  ALOOKUP (compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))
    v = SOME roots /\
  current_pruned_reach (current_frontier_map fn)
    (select_current_live_in T (liveness_analyze fn) fn) v roots y ==>
  y = db.bb_label
Proof
  strip_tac >>
  `!d. MEM d roots ==> d = db.bb_label` by
    metis_tac[current_compute_defs_single_support] >>
  metis_tac[current_single_pruned_reach_local]
QED
