Theory makeSsaCurrentInsertedNonself
Ancestors makeSsaCurrentIngressTokens makeSsaCurrentMergeCertificate
  makeSsaCurrentReinsertionSlots makeSsaCurrentPathBridge
  makeSsaCurrentTokenGraph makeSsaCurrentTokens makeSsaCurrentAnalysis
  makeSsaCurrentPlacementCut makeSsaCurrentSourceCuts
  makeSsaCurrentTreePaths makeSsaCurrentDefs cfgAnalysisProps cfgDefs
  dominatorDefs venomWf venomInst list venomExecProps
  makeSsaCurrentDefaultAudit makeSsaCurrentReinsertionNames
  makeSsaCurrentTraceCertificate makeSsaCurrentCertificate
  makeSsaCurrentAllocation makeSsaCurrentRenameTrace makeSsaCurrentMergeSeed

Theorem current_certificate_inserted_exit_seed:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h ==>
  ?ev. MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
    current_event_exit_env ev v <> CurrentDefault v /\
    current_event_exit_env ev v <> CurrentInserted v h
Proof
  strip_tac >> drule_all current_actual_inserted_exit_seed >> strip_tac >>
  `MEM p (fn_labels fn)` by metis_tac[cfg_analyze_pred_labels] >>
  drule_all current_certificate_event_at >> strip_tac >>
  drule_all current_certificate_static_env >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn)
    eb.bb_label (REVERSE path) p` by metis_tac[current_actual_path_chain] >>
  `ps = REVERSE path` by
    (irule current_token_chain_unique >> metis_tac[current_token_root_idom]) >>
  qexists_tac `ev` >> gvs[current_cfg_edge_preds]
QED

Theorem current_certificate_inserted_nonself_name:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME out ==>
  ?ev. MEM ev events /\ fn_cfg_edge fn (current_event_label ev) h /\
    latest_current_name (current_event_exit_rs ev) v <> out
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  `?old. lookup_block h fn.fn_blocks = SOME old` by
    (gvs[fn_labels_def, MEM_MAP] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       gvs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
  drule_all current_certificate_inserted_prefix >> strip_tac >>
  drule_all current_certificate_event_at >> strip_tac >>
  `MEM (CurrentInserted v h,v) (FLAT (A h))` by
    (simp[current_block_annotations_def, FLAT_APPEND] >>
     metis_tac[current_inserted_annotation_member, lookup_block_label]) >>
  `MEM v V` by
    (`current_event_valid A V ev` by metis_tac[EVERY_MEM] >>
     drule current_event_annotation_owner_covered >> simp[] >>
     disch_then (qspecl_then [`v`, `CurrentInserted v h`] mp_tac) >> gvs[]) >>
  drule_all current_certificate_inserted_exit_seed >> strip_tac >>
  `current_token_name H (current_event_exit_env ev' v) =
     SOME (latest_current_name (current_event_exit_rs ev') v)` by
    (irule (cj 2 current_event_names_accessors) >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all current_certificate_static_env >> strip_tac >>
  qexists_tac `ev'` >> simp[] >>
  qpat_x_assum `!v. current_event_exit_env ev' v = _`
    (fn th => fs[th]) >>
  drule_all current_exit_name_alias_residual >> simp[]
QED
