Theory makeSsaCurrentRootedTokens
Ancestors makeSsaCurrentReinsertionSlots makeSsaCurrentDemandedCut
  makeSsaCurrentLastSite makeSsaCurrentCutTokens makeSsaCurrentLiveTransport
  makeSsaCurrentPathBridge makeSsaCurrentTokenGraph makeSsaCurrentTokens
  makeSsaCurrentSourceCuts makeSsaCurrentPlacementCut makeSsaCurrentDefs
  makeSsaCurrentAnalysis venomWf venomExecProps venomInst cfgWf
  livenessDefs list rich_list relation cfgAnalysisProps

Theorem current_certificate_root_exit:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  MEM ep events /\ current_event_label ep = eb.bb_label ==>
  current_event_exit_env ep v =
    current_block_token fn (current_actual_inserted fn) v eb.bb_label (CurrentDefault v)
Proof
  strip_tac >> drule_all current_certificate_static_env >> strip_tac >>
  drule_all current_actual_path_chain >> strip_tac >>
  `current_inherited_token fn (current_actual_inserted fn) v path = CurrentDefault v` by
    metis_tac[current_actual_root_token, REVERSE_REVERSE] >>
  gvs[]
QED

Theorem current_certificate_site_exit:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  current_changing_site fn (current_actual_inserted fn) v p ==>
  current_event_exit_env ep v =
    current_block_token fn (current_actual_inserted fn) v p t
Proof
  strip_tac >> drule_all current_certificate_static_env >> strip_tac >>
  `MEM p (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[lookup_block_MEM, lookup_block_label]) >>
  metis_tac[current_site_block_constant]
QED

Theorem current_certificate_non_site_live_exit:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  MEM ea events /\ current_event_label ea = a /\
  MEM ep events /\ current_event_label ep = p /\ fn_cfg_edge fn a p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  ~current_changing_site fn (current_actual_inserted fn) v p /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) ==>
  current_event_exit_env ep v = current_event_exit_env ea v
Proof
  strip_tac >>
  `~current_actual_inserted fn v p` by gvs[current_changing_site_def] >>
  `current_phi_cut_clear fn v p` by metis_tac[current_non_site_cut_clear] >>
  `MEM v (live_vars_at (liveness_analyze fn) p
    (LENGTH (collect_phis pb.bb_instructions)))` by
    (irule current_live_exit_to_cut >> simp[] >>
     metis_tac[current_non_site_outputs]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) p = SOME vs /\ MEM v vs` by
    metis_tac[current_selected_live_iff] >>
  `?pa. current_tree_ancestor_path (current_dom_tree fn) a pa /\
    (!w. current_event_exit_env ea w =
      current_block_token fn (current_actual_inserted fn) w a
        (current_inherited_token fn (current_actual_inserted fn) w pa))` by
    metis_tac[current_certificate_static_env] >>
  `?pp. current_tree_ancestor_path (current_dom_tree fn) p pp /\
    (!w. current_event_exit_env ep w =
      current_block_token fn (current_actual_inserted fn) w p
        (current_inherited_token fn (current_actual_inserted fn) w pp))` by
    metis_tac[current_certificate_static_env] >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn)
    eb.bb_label (REVERSE pa) a /\
   current_token_chain (dom_analyze (cfg_analyze fn) fn)
    eb.bb_label (REVERSE pp) p` by metis_tac[current_actual_path_chain] >>
  `current_block_token fn (current_actual_inserted fn) v a
     (current_inherited_token fn (current_actual_inserted fn) v pa) =
   current_inherited_token fn (current_actual_inserted fn) v pp` by
    metis_tac[current_actual_demanded_cut_tokens, REVERSE_REVERSE] >>
  simp[current_non_site_block_token]
QED

Theorem current_certificate_rooted_live_exit:
  !route p ep pb.
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  LRC (fn_cfg_edge fn) route eb.bb_label p /\
  MEM ep events /\ current_event_label ep = p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) /\
  (!b phi. MEM b fn.fn_blocks /\ MEM phi (collect_phis b.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_event_exit_env ep v =
    current_chain_token fn (current_actual_inserted fn) v (route ++ [p]) (CurrentDefault v)
Proof
  ho_match_mp_tac SNOC_INDUCT >> conj_tac
  >- (simp[LRC_def, current_chain_token_def] >> rpt strip_tac >>
      metis_tac[current_certificate_root_exit]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[SNOC_APPEND, current_lrc_append, LRC_def] >> strip_tac >>
  rename1 `fn_cfg_edge fn a p` >>
  rewrite_tac[current_chain_token_append, current_chain_token_def] >>
  Cases_on `current_changing_site fn (current_actual_inserted fn) v p`
  >- (irule current_certificate_site_exit >> metis_tac[]) >>
  `MEM a (fn_labels fn)` by
    (gvs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `?ab. lookup_block a fn.fn_blocks = SOME ab` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  `?ea. MEM ea events /\ current_event_label ea = a` by
    metis_tac[current_certificate_event_at] >>
  `MEM v (live_vars_at (liveness_analyze fn) p
     (LENGTH (collect_phis pb.bb_instructions)))` by
    (irule current_live_exit_to_cut >> simp[] >>
     metis_tac[current_non_site_outputs]) >>
  `MEM v (live_vars_at (liveness_analyze fn) a (LENGTH ab.bb_instructions))` by
    (irule current_live_cut_to_pred_exit >> simp[] >>
     qexistsl_tac [`p`, `pb`] >> simp[] >> conj_tac
     >- metis_tac[lookup_block_MEM] >>
     metis_tac[current_non_site_cut_clear, current_phi_cut_clear_def]) >>
  `current_event_exit_env ea v =
   current_chain_token fn (current_actual_inserted fn) v
     (route ++ [a]) (CurrentDefault v)` by
    (first_x_assum irule >> metis_tac[]) >>
  `current_event_exit_env ep v = current_event_exit_env ea v` by
    (irule current_certificate_non_site_live_exit >> metis_tac[]) >>
  simp[current_non_site_block_token, current_chain_token_append, current_chain_token_def]
QED
