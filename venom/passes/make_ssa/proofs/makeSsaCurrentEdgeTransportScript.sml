Theory makeSsaCurrentEdgeTransport
Ancestors livenessTransferProofs
  makeSsaCurrentDemand makeSsaCurrentAnalysis makeSsaCurrentDemandDominance
  venomExecProps cfgWf venomWf venomInst list
  makeSsaCurrentWfSsa makeSsaCurrentDemandedCut makeSsaCurrentPathBridge

Theorem current_demand_back_range:
  !n i. lookup_block l fn.fn_blocks = SOME bb /\
    i + n <= LENGTH bb.bb_instructions /\
    current_demand fn v l (i + n) /\
    (!j. i <= j /\ j < i + n ==>
      ~MEM v (inst_defs (EL j bb.bb_instructions))) ==>
    current_demand fn v l i
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  irule (cj 3 current_demand_rules) >>
  conj_tac
  >- (qexists_tac `bb` >> simp[] >> decide_tac) >>
  qpat_x_assum `!i. _ ==> current_demand _ _ _ _`
    (qspec_then `SUC i` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> disch_then irule >>
  gvs[arithmeticTheory.ADD_CLAUSES] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem current_demand_edge_no_phi_defs:
  wf_function fn /\
  lookup_block p fn.fn_blocks = SOME pred /\
  lookup_block h fn.fn_blocks = SOME dest /\ fn_cfg_edge fn p h /\
  current_demand fn v h (LENGTH (collect_phis dest.bb_instructions)) /\
  (!j. j < LENGTH (collect_phis dest.bb_instructions) ==>
    ~MEM v (inst_defs (EL j dest.bb_instructions))) ==>
  current_demand fn v p (LENGTH pred.bb_instructions)
Proof
  strip_tac >> irule (cj 4 current_demand_rules) >>
  simp[] >> qexistsl_tac [`dest`, `h`] >> simp[] >>
  conj_tac
  >- (gvs[fn_cfg_edge_def] >>
      fs[wf_function_def, fn_labels_def] >>
      drule MEM_lookup_block >> simp[]) >>
  irule current_demand_back_range >>
  qexistsl_tac [`dest`, `LENGTH (collect_phis dest.bb_instructions)`] >>
  simp[] >> metis_tac[current_collect_phis_length]
QED

Theorem current_edge_unaffected_env:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn p h /\
  MEM pev events /\ current_event_label pev = p /\
  MEM hev events /\ current_event_label hev = h /\
  ~current_actual_inserted fn v h /\ current_phi_cut_clear fn v h /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) h = SOME vs /\ MEM v vs) ==>
  current_event_exit_env pev v = current_event_entry_env hev v
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\
   first_block_no_preds fn` by fs[current_wf_phi_context_def] >>
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
  `current_token_chain (dom_analyze (cfg_analyze fn) fn)
     eb.bb_label (REVERSE ps) p /\
   current_token_chain (dom_analyze (cfg_analyze fn) fn)
     eb.bb_label (REVERSE qs) h` by metis_tac[current_actual_path_chain] >>
  mp_tac (Q.INST [`ps` |-> `REVERSE ps`, `qs` |-> `REVERSE qs`,
    `a` |-> `p`, `b` |-> `h`]
    current_actual_demanded_cut_tokens) >> simp[] >> metis_tac[]
QED

Theorem current_edge_source_cut_no_phi_defs:
  current_source_cut A ev (LENGTH pre + LENGTH (collect_phis old.bb_instructions)) rs E /\
  current_event_label ev = old.bb_label /\
  A old.bb_label = current_block_annotations old pre /\
  (!inst. MEM inst pre ==> ~MEM v inst.inst_outputs) /\
  (!j. j < LENGTH (collect_phis old.bb_instructions) ==>
    ~MEM v (inst_defs (EL j old.bb_instructions))) ==>
  E v = current_event_entry_env ev v
Proof
  strip_tac >>
  `LENGTH (collect_phis old.bb_instructions) <= LENGTH old.bb_instructions` by
    simp[current_collect_phis_length] >>
  drule_all current_wf_source_cut_original_scan >>
  disch_then (qspec_then `v` mp_tac) >>
  `EVERY (\inst. ~MEM v inst.inst_outputs)
    (TAKE (LENGTH (collect_phis old.bb_instructions)) old.bb_instructions)` by
    (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     fs[inst_defs_def] >> metis_tac[]) >>
  simp[makeSsaCurrentTokensTheory.current_original_scan_absent] >> metis_tac[]
QED
