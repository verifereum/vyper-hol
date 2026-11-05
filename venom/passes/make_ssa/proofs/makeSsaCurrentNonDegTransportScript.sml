Theory makeSsaCurrentNonDegTransport
Ancestors
  makeSsaCurrentNonDegPlacement makeSsaCurrentNonDegDefault
  makeSsaCurrentNonDegTokenSources makeSsaCurrentPlacement makeSsaCurrentPlacementCut
  makeSsaCurrentTokenGraph makeSsaCurrentLastSite makeSsaCurrentTokens
  makeSsaCurrentAnalysis makeSsaCurrentFrontier makeSsaCurrentDefs
  venomInst venomWf venomExecProps cfgWf unitShapeDefs dominatorDefs list alist

Theorem current_nondeg_inserted_selected_live:
  current_actual_inserted fn v h ==>
  ?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs
Proof
  simp[current_actual_inserted_def] >> strip_tac >>
  drule current_pruned_reach_live >> simp[current_placement_live_def]
QED

Theorem current_nondeg_inserted_exit_witness:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  first_block_no_phi fn /\ ~blocks_have_leading_phi fn.fn_blocks /\
  entry_block fn = SOME eb /\ current_actual_inserted fn v h /\
  lookup_block h fn.fn_blocks = SOME hb ==>
  ?a b ps qs.
    fn_cfg_edge fn a h /\ fn_cfg_edge fn b h /\
    current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
    current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (a::ps)) <>
      current_inherited_token fn (current_actual_inserted fn) v (REVERSE (b::qs)) /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (a::ps)) <>
      CurrentInserted v h /\
    current_inherited_token fn (current_actual_inserted fn) v (REVERSE (b::qs)) <>
      CurrentInserted v h /\
    (!w. current_inherited_token fn (current_actual_inserted fn) v (REVERSE (a::ps)) <>
      CurrentDefault w) /\
    (!w. current_inherited_token fn (current_actual_inserted fn) v (REVERSE (b::qs)) <>
      CurrentDefault w)
Proof
  rpt gen_tac >> disch_then strip_assume_tac >>
  drule_all nondeg_inserted_graph_witnesses >>
  disch_then strip_assume_tac >>
  rename1 `dominates (dom_analyze (cfg_analyze fn) fn) d a` >>
  rename1 `~dominates (dom_analyze (cfg_analyze fn) fn) d b` >>
  `fn_cfg_edge fn a h /\ fn_cfg_edge fn b h` by
    metis_tac[current_cfg_edge_preds] >>
  `MEM a (fn_labels fn) /\ MEM b (fn_labels fn)` by
    (gvs[fn_cfg_edge_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `MEM d (fn_labels fn)` by metis_tac[current_nondeg_frontier_source_label] >>
  `MEM h (fn_labels fn)` by metis_tac[current_frontier_edge_target_label] >>
  `?ps. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a` by
    metis_tac[current_actual_token_chain] >>
  `?qs. current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b` by
    metis_tac[current_actual_token_chain] >>
  `current_changing_site fn (current_actual_inserted fn) v d` by
    metis_tac[current_changing_site_def] >>
  `current_chain_token fn (current_actual_inserted fn) v (REVERSE ps ++ [a]) (CurrentDefault v) <>
   current_chain_token fn (current_actual_inserted fn) v (REVERSE qs ++ [b]) (CurrentDefault v)` by
    metis_tac[current_nondeg_actual_exit_tokens_distinct] >>
  `current_chain_token fn (current_actual_inserted fn) v (REVERSE ps ++ [a]) (CurrentDefault v) <>
    CurrentInserted v h` by
    (Cases_on `d = h`
     >- (gvs[] >> irule current_nondeg_original_ancestor_exit_nonself >>
         goal_assum (drule_at Any) >> simp[] >>
         `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
           (irule venomExecPropsTheory.MEM_lookup_block >>
            fs[wf_function_def, fn_labels_def]) >> gvs[] >> metis_tac[]) >>
     `~dominates (dom_analyze (cfg_analyze fn) fn) d h` by
       (gvs[current_frontier_edge_def] >>
        drule_all current_frontier_elim >> simp[strict_dominates_def] >>
        metis_tac[]) >>
     metis_tac[current_nondeg_dominated_exit_nonself]) >>
  `current_chain_token fn (current_actual_inserted fn) v (REVERSE qs ++ [b]) (CurrentDefault v) <>
    CurrentInserted v h` by
    metis_tac[current_nondeg_outside_exit_nonself] >>
  `?ab. lookup_block a fn.fn_blocks = SOME ab` by
    (qpat_x_assum `MEM a (fn_labels fn)` mp_tac >>
     simp[fn_labels_def, MEM_MAP] >>
     disch_then (qx_choose_then `ab` strip_assume_tac) >>
     qexists_tac `ab` >> irule venomExecPropsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `?pred_b_block. lookup_block b fn.fn_blocks = SOME pred_b_block` by
    (qpat_x_assum `MEM b (fn_labels fn)` mp_tac >>
     simp[fn_labels_def, MEM_MAP] >>
     disch_then (qx_choose_then `pred_b_member` strip_assume_tac) >>
     qexists_tac `pred_b_member` >> irule venomExecPropsTheory.MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def]) >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs` by
    metis_tac[current_nondeg_inserted_selected_live] >>
  `!w. current_inherited_token fn (current_actual_inserted fn) v (REVERSE (a::ps)) <>
    CurrentDefault w` by
    (gen_tac >> irule current_nondeg_live_pred_chain_nondefault >>
     goal_assum (drule_at Any) >> gvs[] >> metis_tac[]) >>
  `!w. current_inherited_token fn (current_actual_inserted fn) v (REVERSE (b::qs)) <>
    CurrentDefault w` by
    (gen_tac >> irule current_nondeg_live_pred_chain_nondefault >>
     goal_assum (drule_at Any) >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`a`, `b`, `ps`, `qs`] >>
  simp[current_inherited_token_def] >>
  metis_tac[current_inherited_token_def, REVERSE_DEF]
QED
