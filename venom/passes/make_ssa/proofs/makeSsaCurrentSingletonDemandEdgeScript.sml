Theory makeSsaCurrentSingletonDemandEdge
Ancestors
  makeSsaCurrentEdgeTransport makeSsaCurrentSingletonCut
  makeSsaCurrentDemandedCut makeSsaCurrentDemandDominance
  makeSsaCurrentPlacementCut makeSsaCurrentWfSsa makeSsaCurrentAvailability
  makeSsaCurrentLastSite makeSsaCurrentAnalysis makeSsaHelper
  makeSsaCurrentDominanceBridge makeSsaCurrentPathBridge cfgWf
  dominatorDefs venomInst venomWf venomExecProps list

Theorem current_single_demand_clear_definition[local]:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\ all_reachable fn /\
  lookup_block h fn.fn_blocks = SOME old /\ current_phi_cut_clear fn v h /\
  current_demand fn v h (LENGTH (collect_phis old.bb_instructions)) /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label h
Proof
  strip_tac >>
  `MEM h (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `fn_reachable fn h` by
    (fs[all_reachable_def, fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `current_available fn v h (LENGTH (collect_phis old.bb_instructions))` by
    (irule current_demand_available >> metis_tac[]) >>
  drule_all current_available_definition >> strip_tac >>
  `db <> old` by
    (strip_tac >> gvs[] >> drule_all current_available_local_index >> strip_tac >>
     fs[current_phi_cut_clear_def, inst_defs_def] >> metis_tac[]) >>
  `fn_dominates fn db.bb_label h` by
    (irule current_available_unique_dominates >> metis_tac[]) >>
  `MEM db.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  `db.bb_label <> h` by
    (strip_tac >>
     `lookup_block h fn.fn_blocks = SOME db` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  qexistsl_tac [`db`, `di`] >> simp[strict_dominates_def] >>
  metis_tac[current_semantic_dominates]
QED

Theorem current_single_demand_sites[local]:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\ all_reachable fn /\
  first_block_no_preds fn /\ entry_block fn = SOME eb /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  blocks_have_leading_phi fn.fn_blocks ==>
  current_changing_site fn (current_actual_inserted fn) v db.bb_label /\
  (!l. current_changing_site fn (current_actual_inserted fn) v l ==> l = db.bb_label)
Proof
  strip_tac >> conj_tac
  >- (simp[current_changing_site_def] >> metis_tac[]) >>
  simp[current_changing_site_def] >> rpt strip_tac
  >- (irule current_actual_inserted_single_local >> metis_tac[]) >>
  metis_tac[makeSsaCurrentOccurrenceTheory.current_single_def_occurrence]
QED

Theorem current_phi_operand_demand_edge_env:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  MEM pev events /\ current_event_label pev = p /\
  MEM hev events /\ current_event_label hev = h /\
  lookup_block h fn.fn_blocks = SOME old /\ current_phi_cut_clear fn v h /\
  current_demand fn v h (LENGTH (collect_phis old.bb_instructions)) /\
  (?pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_event_exit_env pev v = current_event_entry_env hev v
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\ all_reachable fn /\
   first_block_no_preds fn /\ fn_phi_operands_single_def fn /\
   current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    (irule current_phi_operand_single_bound >> metis_tac[]) >>
  `blocks_have_leading_phi fn.fn_blocks` by
    metis_tac[current_phi_operand_has_leading_phi] >>
  drule_all current_single_demand_clear_definition >> strip_tac >>
  drule_all current_single_demand_sites >> strip_tac >>
  drule current_wf_precleanup_structural >> strip_tac >>
  `?ps. current_tree_ancestor_path (current_dom_tree fn) p ps /\
    (!w. current_event_exit_env pev w =
      current_block_token fn (current_actual_inserted fn) w p
        (current_inherited_token fn (current_actual_inserted fn) w ps))` by
    metis_tac[current_wf_certificate_static_entry] >>
  `?qs. current_tree_ancestor_path (current_dom_tree fn) h qs /\
    (!w. current_event_entry_env hev w =
      current_inherited_token fn (current_actual_inserted fn) w qs)` by
    metis_tac[current_wf_certificate_static_entry] >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (REVERSE ps) p /\
   current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (REVERSE qs) h` by
    metis_tac[current_actual_path_chain] >>
  `MEM db.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]) >>
  drule_all current_single_site_edge_tokens >> simp[]
QED
