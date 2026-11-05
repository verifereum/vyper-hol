Theory makeSsaCurrentEventTransport
Ancestors makeSsaCurrentTreePaths makeSsaCurrentPathBridge
  makeSsaCurrentDemandedCut list

Theorem current_actual_event_live_transport:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\
  LENGTH fn.fn_blocks = LENGTH bbs /\
  LIST_REL (\pair anns. current_block_provenance fn (FST pair) (SND pair) anns)
    (ZIP (fn.fn_blocks,bbs)) annsss /\
  (!old. MEM old fn.fn_blocks ==> lookup_block old.bb_label fn.fn_blocks = SOME old) /\
  (!l. MEM l (dom_tree_labels (current_dom_tree fn)) ==>
    IS_SOME (lookup_block l bbs)) /\
  current_tree_trace (current_annotation_map bbs annsss) sm (current_dom_tree fn)
    s rs bbs H CurrentDefault visited ctrs' s' bbs' H' visited' events /\
  MEM ea events /\ MEM ebv events /\
  fn_cfg_edge fn (current_event_label ea) (current_event_label ebv) /\
  ~current_actual_inserted fn v (current_event_label ebv) /\
  current_phi_cut_clear fn v (current_event_label ebv) /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) (current_event_label ebv) = SOME vs /\ MEM v vs) ==>
  current_event_exit_env ea v = current_event_entry_env ebv v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_provenance_tree_static_env >>
  disch_then (qx_choose_then `qs` strip_assume_tac) >>
  qpat_x_assum `MEM ebv events` kall_tac >>
  drule_all current_provenance_tree_static_env >>
  disch_then (qx_choose_then `ps` strip_assume_tac) >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label
    (REVERSE ps) (current_event_label ea)` by
      metis_tac[current_actual_path_chain] >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label
    (REVERSE qs) (current_event_label ebv)` by
      metis_tac[current_actual_path_chain] >>
  drule_all current_actual_demanded_cut_tokens >>
  simp[REVERSE_REVERSE]
QED
