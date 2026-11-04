Theory makeSsaCurrentIngressTokens
Ancestors makeSsaCurrentIngress makeSsaCurrentDefaultOrigin
  makeSsaCurrentMergeSeed makeSsaCurrentLastSite makeSsaCurrentExitTokens
  makeSsaCurrentTokenOwnership makeSsaCurrentFrontier makeSsaCurrentGraphCut
  makeSsaCurrentTokenGraph makeSsaCurrentTokens makeSsaCurrentAnalysis
  dominatorDefs dominatorAnalysisProps cfgAnalysisProps cfgDefs
  makeSsaCurrentPlacementCut makeSsaCurrentPlacement makeSsaCurrentDefs
  alist venomInst venomWf venomExecProps list

Theorem current_block_site_excludes:
  lookup_block d fn.fn_blocks = SOME bb /\
  ((?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) \/
   (ins v d /\ d <> h)) ==>
  current_block_token fn ins v d t <> CurrentDefault v /\
  current_block_token fn ins v d t <> CurrentInserted v h
Proof
  strip_tac
  >- (metis_tac[current_block_token_original, current_token_distinct]) >>
  Cases_on `?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs`
  >- (metis_tac[current_block_token_original, current_token_distinct]) >>
  `EVERY (\inst. ~MEM v inst.inst_outputs) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  simp[current_block_token_def, current_original_scan_absent]
QED

Theorem current_generating_site_exit_excludes:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM p (fn_labels fn) /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p /\
  dominates (dom_analyze (cfg_analyze fn) fn) d p /\
  ~strict_dominates (dom_analyze (cfg_analyze fn) fn) d h /\
  lookup_block d fn.fn_blocks = SOME bb /\
  ((?inst. MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) \/
   (ins v d /\ d <> h)) ==>
  current_block_token fn ins v p
    (current_inherited_token fn ins v (REVERSE ps)) <> CurrentDefault v /\
  current_block_token fn ins v p
    (current_inherited_token fn ins v (REVERSE ps)) <> CurrentInserted v h
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM d (p::ps)` by
    (drule_all current_actual_chain_membership >>
     simp[strict_dominates_def] >> metis_tac[]) >>
  drule_all current_token_chain_member_suffix >> strip_tac >>
  `ALL_DISTINCT (pre ++ d::ds)` by metis_tac[current_actual_chain_distinct] >>
  `~MEM h pre` by
    (strip_tac >>
     `dominates (dom_analyze (cfg_analyze fn) fn) d h` by
       metis_tac[current_chain_prefix_dominated] >>
     gvs[ALL_DISTINCT_APPEND, strict_dominates_def] >> metis_tac[]) >>
  `!t. current_block_token fn ins v d t <> CurrentDefault v /\
       current_block_token fn ins v d t <> CurrentInserted v h` by
    metis_tac[current_block_site_excludes] >>
  rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
  `REVERSE ps ++ [p] = REVERSE ds ++ [d] ++ REVERSE pre` by
    (pure_rewrite_tac[GSYM (CONJUNCT2 REVERSE_DEF)] >>
     asm_rewrite_tac[REVERSE_APPEND] >> simp[]) >>
  pure_rewrite_tac[GSYM current_inherited_token_def] >>
  once_rewrite_tac[GSYM current_inherited_token_step] >>
  pure_rewrite_tac[current_inherited_token_def] >>
  qpat_x_assum `REVERSE ps ++ [p] = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[current_chain_token_append] >>
  pure_rewrite_tac[current_chain_token_def] >>
  conj_tac
  >- (simp[current_chain_token_default] >> metis_tac[]) >>
  strip_tac >>
  qpat_x_assum `current_chain_token _ _ _ _ _ = CurrentInserted _ _` mp_tac >>
  qmatch_goalsub_abbrev_tac `current_chain_token fn ins v path tok` >>
  `tok <> CurrentInserted v h /\ ~MEM h path` by simp[Abbr `tok`, Abbr `path`] >>
  metis_tac[current_chain_inserted_origin]
QED

Theorem current_actual_inserted_exit_seed:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h ==>
  ?p ps. MEM p (cfg_preds_of (cfg_analyze fn) h) /\
    current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p /\
    current_block_token fn (current_actual_inserted fn) v p
      (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) <>
      CurrentDefault v /\
    current_block_token fn (current_actual_inserted fn) v p
      (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) <>
      CurrentInserted v h
Proof
  strip_tac >> drule_all current_actual_inserted_ingress >>
  disch_then (qx_choose_then `d` assume_tac) >>
  `MEM d (fn_labels fn)` by
    (gvs[current_frontier_edge_def] >> imp_res_tac ALOOKUP_MEM >>
     gvs[current_frontier_map_def, current_query_map_def, MEM_MAP] >> metis_tac[]) >>
  `?p. MEM p (cfg_preds_of (cfg_analyze fn) h) /\
       dominates (dom_analyze (cfg_analyze fn) fn) d p /\
       ~strict_dominates (dom_analyze (cfg_analyze fn) fn) d h` by
    (irule current_frontier_elim >> simp[] >>
     gvs[current_frontier_edge_def] >> metis_tac[]) >>
  `MEM p (fn_labels fn)` by metis_tac[cfg_analyze_pred_labels] >>
  `?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p` by
    metis_tac[current_actual_token_chain] >>
  qexistsl_tac [`p`, `ps`] >> simp[] >>
  irule current_generating_site_exit_excludes >> simp[] >>
  `?bb. lookup_block d fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP] >>
     `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
       gvs[wf_function_def, fn_labels_def] >>
     metis_tac[MEM_lookup_block]) >>
  qexistsl_tac [`bb`, `d`] >> simp[] >>
  gvs[] >> disj1_tac >>
  `lookup_block bb'.bb_label fn.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  metis_tac[optionTheory.SOME_11]
QED
