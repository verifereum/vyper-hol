Theory makeSsaCurrentInsertedNonself
Ancestors makeSsaCurrentIngressTokens makeSsaCurrentMergeCertificate
  makeSsaCurrentReinsertionSlots makeSsaCurrentPathBridge
  makeSsaCurrentTokenGraph makeSsaCurrentTokens makeSsaCurrentAnalysis
  makeSsaCurrentPlacementCut makeSsaCurrentSourceCuts
  makeSsaCurrentTreePaths makeSsaCurrentDefs cfgAnalysisProps cfgDefs
  dominatorDefs venomWf venomInst list venomExecProps
  makeSsaCurrentDefaultAudit makeSsaCurrentReinsertionNames
  makeSsaCurrentTraceCertificate makeSsaCurrentCertificate
  makeSsaCurrentFinalSlots makeSsaCurrentCleanupClassify
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

Theorem current_certificate_inserted_nonself_slots:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) ==>
  ?slots.
    FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\p. (p,v)) ps)) events = current_phi_slots slots /\
    ?p n. MEM (p,n) slots /\ n <> out
Proof
  strip_tac >> drule_all current_certificate_inserted_nonself_name >> strip_tac >>
  `MEM h (fn_labels fn)` by metis_tac[current_actual_inserted_support] >>
  qexists_tac `MAP (\slot. FOLDL (\slot ev.
    current_event_pair_action (current_succ_map fn) h ev slot) slot events)
      (MAP (\p. (p,v)) ps)` >>
  simp[current_event_fold_slots] >>
  `MEM (current_event_label ev) ps` by
    gvs[ALOOKUP_current_pred_map, current_cfg_edge_preds] >>
  `ALL_DISTINCT (MAP current_event_label events)` by
    metis_tac[current_certificate_event_labels_distinct] >>
  `MEM (current_event_label ev) (fn_labels fn)` by
    (fs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM h (case ALOOKUP (current_succ_map fn) (current_event_label ev) of
      NONE => [] | SOME ss => ss)` by
    simp[ALOOKUP_current_succ_map, GSYM current_cfg_edge_succs] >>
  `FOLDL (\slot ev. current_event_pair_action (current_succ_map fn) h ev slot)
      (current_event_label ev,v) events =
      (current_event_label ev,latest_current_name (current_event_exit_rs ev) v)` by
    metis_tac[current_event_fold_pair_unique, pairTheory.FST, pairTheory.SND] >>
  qexistsl_tac [`current_event_label ev`,
    `latest_current_name (current_event_exit_rs ev) v`] >>
  simp[MEM_MAP] >>
  qexists_tac `(current_event_label ev,v)` >> simp[] >> metis_tac[]
QED

Theorem current_certificate_inserted_not_nop:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  ps = (case ALOOKUP (current_pred_map fn) h of NONE => [] | SOME ps0 => ps0) /\
  i.inst_opcode = PHI /\ i.inst_outputs = [out] /\
  i.inst_operands =
    FOLDL (\ops ev. current_event_operand_action (current_succ_map fn) h ev ops)
      (current_phi_slots (MAP (\p. (p,v)) ps)) events ==>
  (simplify_current_phi i).inst_opcode <> NOP
Proof
  strip_tac >> drule_all current_certificate_inserted_nonself_slots >> strip_tac >>
  `i.inst_operands = current_phi_slots slots` by metis_tac[] >>
  `FILTER (\n. n <> out) (MAP SND slots) <> []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  drule current_phi_slots_nop_iff >>
  disch_then (qspecl_then [`slots`, `out`,
    `FILTER (\n. n <> out) (MAP SND slots)`] mp_tac) >> simp[]
QED
