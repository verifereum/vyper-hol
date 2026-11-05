Theory makeSsaCurrentNonDegCertificate
Ancestors
  makeSsaCurrentTraceCertificate makeSsaCurrentTreeTrace
  makeSsaCurrentAllocation makeSsaCurrentCertificate
  makeSsaCurrentDefs makeSsaCurrentProps venomWf venomInst list

Theorem current_nondeg_actual_initial_trace_names:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  defs = compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))) /\
  add_phi_nodes_supply s (current_frontier_map fn) (current_pred_map fn)
    (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) fn.fn_blocks defs = (bbs1,s1) /\
  rename_current_blocks s1 (init_current_rename_state defs) bbs1
    (current_succ_map fn) (current_dom_tree fn) = (ctrs',s',bbs') ==>
  ?annsss H' visited' events.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs1)) annsss /\
    LENGTH fn.fn_blocks = LENGTH bbs1 /\
    (!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
    (!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs1)) /\
    ALL_DISTINCT (dom_tree_labels (current_dom_tree fn)) /\
    current_tree_trace (current_annotation_map bbs1 annsss) (current_succ_map fn)
      (current_dom_tree fn) s1 (init_current_rename_state defs) bbs1
      [] CurrentDefault [] ctrs' s' bbs' H' visited' events /\
    EVERY (current_event_names H' (FLAT (MAP block_ir_vars bbs1))) events /\
    current_history_valid (FLAT (MAP block_ir_vars bbs1)) H'
Proof
  strip_tac >>
  `MAP (\b. b.bb_label) bbs1 = MAP (\b. b.bb_label) fn.fn_blocks /\
   ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs1)) /\
   ssa_vars_covered s1 (MAP FST defs)` by
    (irule current_insertion_initial_supply >> metis_tac[]) >>
  `ALL_DISTINCT (dom_tree_labels (current_dom_tree fn))` by
    metis_tac[current_actual_tree_labels_distinct] >>
  `!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==> IS_SOME (lookup_block l bbs1)` by
    metis_tac[current_actual_tree_lookup_coverage] >>
  `!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old` by
    (rpt strip_tac >> irule venomExecPropsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `?annsss H' visited' events.
    LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
      (ZIP (fn.fn_blocks,bbs1)) annsss /\
    ALL_DISTINCT (MAP FST (FLAT (FLAT annsss))) /\
    current_tree_trace (current_annotation_map bbs1 annsss) (current_succ_map fn)
      (current_dom_tree fn) s1 (init_current_rename_state defs) bbs1
      [] CurrentDefault [] ctrs' s' bbs' H' visited' events` by
    (irule current_actual_tree_trace >> metis_tac[]) >>
  `LENGTH fn.fn_blocks = LENGTH bbs1` by metis_tac[LENGTH_MAP] >>
  drule_all current_provenance_initial_tree_names >> strip_tac >>
  qexistsl_tac [`annsss`, `H'`, `visited'`, `events`] >>
  fs[current_allocation_consistent_def]
QED
