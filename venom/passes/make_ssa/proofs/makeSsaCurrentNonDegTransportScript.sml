Theory makeSsaCurrentNonDegTransport
Ancestors
  makeSsaCurrentNonDegPlacement makeSsaCurrentNonDegDefault
  makeSsaCurrentNonDegTokenSources makeSsaCurrentPlacement makeSsaCurrentPlacementCut
  makeSsaCurrentTokenGraph makeSsaCurrentLastSite makeSsaCurrentTokens
  makeSsaCurrentAnalysis makeSsaCurrentFrontier makeSsaDefs
  makeSsaCurrentWfSsa makeSsaCurrentPathBridge makeSsaCurrentCertificate
  makeSsaCurrentEdgeTrace makeSsaCurrentAllocation
  makeSsaCurrentLiveTransport livenessDefs o1PassContract
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

Theorem current_nondeg_event_exit_chain:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  MEM ev events /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps (current_event_label ev) ==>
  current_event_exit_env ev v =
  current_inherited_token fn (current_actual_inserted fn) v
    (REVERSE (current_event_label ev :: ps))
Proof
  strip_tac >> drule_all current_wf_certificate_static_entry >> strip_tac >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label
    (REVERSE path) (current_event_label ev)` by
    metis_tac[current_actual_path_chain] >>
  `ps = REVERSE path` by
    metis_tac[current_token_chain_unique, current_token_root_idom] >>
  simp[REVERSE_DEF, current_inherited_token_step]
QED

Theorem current_nondeg_slots_index_member:
  !pairs i. i < LENGTH pairs /\
    EL (2 * i) (current_phi_slots pairs) = Label p /\
    EL (2 * i + 1) (current_phi_slots pairs) = Var n ==>
    MEM (p,n) (phi_pairs (current_phi_slots pairs))
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> Cases_on `i` >>
  simp[current_phi_slots_def, phi_pairs_def, arithmeticTheory.MULT_CLAUSES,
       arithmeticTheory.ADD_CLAUSES] >> rpt strip_tac >>
  `2 * n' + 2 = SUC (SUC (2 * n'))` by decide_tac >>
  `2 * n' + 3 = SUC (SUC (2 * n' + 1))` by decide_tac >>
  gvs[EL, current_phi_slots_def] >> metis_tac[]
QED

Theorem current_nondeg_inserted_pred_name:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  fn_cfg_edge fn p h /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps p ==>
  ?n. current_token_name H
    (current_inherited_token fn (current_actual_inserted fn) v (REVERSE (p::ps))) = SOME n /\
    MEM (p,n) (phi_pairs (EL q new.bb_instructions).inst_operands)
Proof
  strip_tac >>
  `wf_function fn /\ all_reachable fn /\
   current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  `current_structural_certificate s fn
    (fn with fn_blocks := simplify_current_phis_if (blocks_have_leading_phi fn.fn_blocks) renamed)
    s' A H events` by
    (simp[current_wf_precleanup_certificate_stages] >> metis_tac[]) >>
  drule_all current_wf_inserted_phi_slots >> strip_tac >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `MAP FST pairs = cfg_preds_of (cfg_analyze fn) h` by
    (drule ALOOKUP_current_pred_map >> strip_tac >> gvs[]) >>
  `MEM p (MAP FST pairs)` by metis_tac[current_cfg_edge_preds] >>
  `?i. i < LENGTH pairs /\ FST (EL i pairs) = p` by
    (fs[MEM_EL] >> metis_tac[EL_MAP, LENGTH_MAP]) >>
  `i < LENGTH (MAP FST pairs) /\ EL i (MAP FST pairs) = p` by
    simp[EL_MAP] >>
  drule_all current_wf_inserted_phi_slot >> strip_tac >>
  `current_event_exit_env ev v = current_inherited_token fn
    (current_actual_inserted fn) v (REVERSE (p::ps))` by
    (qpat_assum `current_event_label ev = p` (fn th => rewrite_tac[GSYM th]) >>
     irule current_nondeg_event_exit_chain >> metis_tac[]) >>
  qexists_tac `n` >> conj_tac >- metis_tac[] >>
  simp[] >> irule current_nondeg_slots_index_member >> metis_tac[]
QED

Theorem current_nondeg_inserted_phi:
  current_wf_phi_context s fn renamed s' A H events /\
  ~blocks_have_leading_phi fn.fn_blocks /\ entry_block fn = SOME eb /\
  current_wf_inserted_phi_at A renamed h q v /\
  lookup_block h fn.fn_blocks = SOME old /\ lookup_block h renamed = SOME new /\
  (EL q new.bb_instructions).inst_outputs = [out] ==>
  ?p n r m. MEM (p,n) (phi_pairs (EL q new.bb_instructions).inst_operands) /\
    MEM (r,m) (phi_pairs (EL q new.bb_instructions).inst_operands) /\
    n <> m /\ n <> out /\ m <> out
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
   first_block_no_phi fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
   current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_inserted_phi_prefix >> strip_tac >>
  drule_all current_nondeg_inserted_exit_witness >> strip_tac >>
  `?n. current_token_name H (current_inherited_token fn (current_actual_inserted fn) v
    (REVERSE (a::ps))) = SOME n /\
    MEM (a,n) (phi_pairs (EL q new.bb_instructions).inst_operands)` by
    (irule current_nondeg_inserted_pred_name >> metis_tac[]) >>
  `?m. current_token_name H (current_inherited_token fn (current_actual_inserted fn) v
    (REVERSE (b::qs))) = SOME m /\
    MEM (b,m) (phi_pairs (EL q new.bb_instructions).inst_operands)` by
    (irule current_nondeg_inserted_pred_name >> metis_tac[]) >>
  `current_token_name H (CurrentInserted v h) = SOME out` by
    (drule_all current_wf_inserted_phi_output >> simp[]) >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `n <> m` by metis_tac[current_allocated_name_injective] >>
  `n <> out` by metis_tac[current_allocated_name_injective, current_token_distinct] >>
  `m <> out` by metis_tac[current_allocated_name_injective, current_token_distinct] >>
  qexistsl_tac [`a`, `n`, `b`, `m`] >> simp[]
QED

Theorem current_nondeg_no_original_phi:
  wf_function fn /\ ~blocks_have_leading_phi fn.fn_blocks ==>
  ~current_wf_original_phi_at fn A renamed h k q slots
Proof
  strip_tac >> strip_tac >> fs[current_wf_original_phi_at_def] >>
  `collect_phis old.bb_instructions = []` by metis_tac[current_no_leading_phi_cut] >>
  `bb_well_formed old` by metis_tac[wf_function_def, lookup_block_MEM] >>
  Cases_on `old.bb_instructions` >> gvs[collect_phis_def] >>
  Cases_on `k` >> gvs[bb_well_formed_def, collect_phis_def] >>
  qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[] >>
  qpat_x_assum `(if _ then _ else _) = []` mp_tac >> IF_CASES_TAC >> simp[]
QED

Theorem current_nondeg_phi_free_context:
  current_wf_phi_context s fn renamed s' A H events /\
  ~blocks_have_leading_phi fn.fn_blocks /\ entry_block fn = SOME eb ==>
  fn_phis_non_degenerate (fn with fn_blocks := renamed)
Proof
  strip_tac >>
  `wf_function fn` by fs[current_wf_phi_context_def] >>
  simp[fn_phis_non_degenerate_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
  rpt gen_tac >> strip_tac >>
  rename1 `MEM new renamed` >>
  `?q. q < LENGTH new.bb_instructions /\ inst = EL q new.bb_instructions` by
    metis_tac[MEM_EL] >>
  drule_all current_wf_phi_context_lookup >> strip_tac >>
  qpat_x_assum `inst = EL q _` SUBST_ALL_TAC >>
  `?v. current_wf_inserted_phi_at A renamed new.bb_label q v` by
    (drule_all current_wf_phi_occurrence_provenance >>
     metis_tac[current_nondeg_no_original_phi]) >>
  drule_all current_nondeg_inserted_phi >> metis_tac[]
QED

Theorem current_nondeg_phi_free_run:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  ~blocks_have_leading_phi fn.fn_blocks ==>
  fn_phis_non_degenerate fn'
Proof
  strip_tac >> Cases_on `entry_block fn`
  >- (gvs[make_ssa_current_fn_def, fn_entry_label_def, make_ssa_input_ok_def]) >>
  rename1 `entry_block fn = SOME eb` >>
  `all_reachable fn` by fs[make_ssa_input_ok_def] >>
  drule_all current_wf_named_structural_certificate >> strip_tac >>
  drule (iffLR current_wf_precleanup_certificate_stages) >> strip_tac >>
  `current_wf_phi_context s fn renamed s' A H events` by
    (irule current_wf_phi_context_intro >> fs[make_ssa_input_ok_def] >> metis_tac[]) >>
  drule_all current_nondeg_phi_free_context >>
  gvs[simplify_current_phis_if_def]
QED
