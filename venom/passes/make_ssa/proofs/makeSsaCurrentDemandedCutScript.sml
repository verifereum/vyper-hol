Theory makeSsaCurrentDemandedCut
Ancestors
  makeSsaCurrentSingletonCut makeSsaCurrentPlacementCut makeSsaCurrentCutTokens
  makeSsaCurrentPlacement
  makeSsaCurrentSelectedLive makeSsaCurrentOccurrence makeSsaCurrentLastSite
  makeSsaCurrentDominanceBridge makeSsaCurrentAnalysis makeSsaDefs
  livenessTransferProofs livenessDefs venomWf venomInst venomExecProps cfgWf dominatorDefs
  list alist cfgCorrectnessProof

Theorem current_phi_operand_single_bound:
  fn_phi_operands_single_def fn /\
  MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) /\
  MEM v (MAP SND (phi_pairs phi.inst_operands)) ==>
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1
Proof
  strip_tac >> drule collect_phis_mem >> strip_tac >>
  gvs[fn_phi_operands_single_def_def, MEM_MAP] >>
  PairCases_on `y` >> gvs[] >> metis_tac[]
QED

Theorem current_phi_operand_has_leading_phi:
  !bbs pb phi. MEM pb bbs /\ MEM phi (collect_phis pb.bb_instructions) ==>
  blocks_have_leading_phi bbs
Proof
  Induct >- simp[] >> rpt gen_tac >> simp[blocks_have_leading_phi_def] >>
  Cases_on `h.bb_instructions` >> simp[]
  >- (strip_tac >> gvs[collect_phis_def] >> metis_tac[]) >>
  rename1 `inst::rest` >> Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  strip_tac >> gvs[collect_phis_def] >> metis_tac[]
QED

Theorem current_actual_exceptional_cut_tokens:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  ~current_actual_inserted fn v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  (?pb phi. MEM pb fn.fn_blocks /\ MEM phi (collect_phis pb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_block_token fn (current_actual_inserted fn) v a
    (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs)
Proof
  strip_tac >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    metis_tac[current_phi_operand_single_bound] >>
  `blocks_have_leading_phi fn.fn_blocks` by
    metis_tac[current_phi_operand_has_leading_phi] >>
  `MEM b (fn_labels fn)` by
    metis_tac[current_cfg_edge_succs, cfgCorrectnessProofTheory.cfg_analyze_succ_labels] >>
  `fn_reachable fn b` by
    (gvs[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `?bb. lookup_block b fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP, wf_function_def] >> metis_tac[MEM_lookup_block]) >>
  gvs[] >> drule_all current_selected_live_single_definition >> strip_tac >>
  `db <> bb` by
    (strip_tac >> gvs[current_phi_cut_clear_def, inst_defs_def] >> metis_tac[]) >>
  `db.bb_label <> b` by
    (strip_tac >>
     `lookup_block b fn.fn_blocks = SOME db` by
       (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >> gvs[]) >>
  `MEM db.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label b` by
    (simp[strict_dominates_def] >> metis_tac[current_semantic_dominates]) >>
  irule current_single_site_edge_tokens >> simp[] >>
  qexistsl_tac [`b`, `db.bb_label`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[current_changing_site_def]
      >- metis_tac[current_actual_inserted_single_local] >>
      metis_tac[current_single_def_occurrence]) >>
  simp[current_changing_site_def] >> metis_tac[]
QED

Theorem current_actual_demanded_cut_tokens:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_phi_operands_single_def fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ fn_cfg_edge fn a b /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label ps a /\
  current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label qs b /\
  ~current_actual_inserted fn v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) ==>
  current_block_token fn (current_actual_inserted fn) v a
    (current_inherited_token fn (current_actual_inserted fn) v (REVERSE ps)) =
  current_inherited_token fn (current_actual_inserted fn) v (REVERSE qs)
Proof
  strip_tac >>
  Cases_on `?pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) /\
    MEM v (MAP SND (phi_pairs phi.inst_operands))`
  >- metis_tac[current_actual_exceptional_cut_tokens] >>
  irule current_cut_ordinary_token_equality >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> irule current_actual_inserted_closed >>
      simp[current_placement_live_def] >> metis_tac[]) >>
  qexists_tac `b` >> simp[] >> metis_tac[]
QED
