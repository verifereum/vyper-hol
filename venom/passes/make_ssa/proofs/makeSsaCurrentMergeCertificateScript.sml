Theory makeSsaCurrentMergeCertificate
Ancestors
  makeSsaCurrentMergeSeed makeSsaCurrentReinsertionSlots
  makeSsaCurrentPathBridge makeSsaCurrentAnalysis cfgAnalysisProps
  makeSsaCurrentTokens makeSsaCurrentTreePaths makeSsaCurrentSourceCuts
  makeSsaCurrentDefs dominatorDefs cfgDefs venomWf venomInst list

Theorem current_certificate_nonself_predecessor:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h ==>
  ?p ev path.
    fn_cfg_edge fn p h /\ MEM p (fn_labels fn) /\
    MEM p (cfg_preds_of (cfg_analyze fn) h) /\
    MEM ev events /\ current_event_label ev = p /\
    current_tree_ancestor_path (current_dom_tree fn) p path /\
    ~dominates (dom_analyze (cfg_analyze fn) fn) h p /\
    current_event_exit_env ev v =
      current_block_token fn (current_actual_inserted fn) v p
        (current_inherited_token fn (current_actual_inserted fn) v path) /\
    current_event_exit_env ev v <> CurrentInserted v h
Proof
  strip_tac >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  `h <> eb.bb_label` by metis_tac[current_actual_inserted_nonentry] >>
  drule_all current_nonentry_nonself_predecessor >>
  disch_then (qspecl_then [`v`, `current_actual_inserted fn`] mp_tac) >>
  strip_tac >>
  `MEM p (fn_labels fn)` by metis_tac[cfg_analyze_reachable_in_labels] >>
  drule_all current_certificate_event_at >> strip_tac >>
  drule_all current_certificate_static_env >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn)
    eb.bb_label (REVERSE path) p` by metis_tac[current_actual_path_chain] >>
  qexistsl [`p`, `ev`, `path`] >>
  gvs[current_cfg_edge_preds] >> metis_tac[REVERSE_REVERSE]
QED
