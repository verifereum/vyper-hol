Theory makeSsaCurrentLastSite
Ancestors
  makeSsaCurrentGraphCut makeSsaCurrentLiveTransport makeSsaCurrentFrontier
  makeSsaCurrentAnalysis makeSsaCurrentSelectedLive makeSsaCurrentDefs
  venomInst venomWf venomExecProps cfgAnalysisProps dominatorDefs
  list rich_list alist arithmetic makeSsaCurrentDemandDominance

Definition current_changing_site_def:
  current_changing_site fn ins v l <=> ins v l \/
    ?bb inst. MEM bb fn.fn_blocks /\ bb.bb_label = l /\
      MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs
End

Definition current_phi_cut_clear_def:
  current_phi_cut_clear fn v l <=>
    !bb k. lookup_block l fn.fn_blocks = SOME bb /\
      k < LENGTH (collect_phis bb.bb_instructions) ==>
      ~MEM v (inst_defs (EL k bb.bb_instructions))
End

Theorem current_non_site_outputs:
  ~current_changing_site fn ins v l /\
  lookup_block l fn.fn_blocks = SOME bb /\ k < LENGTH bb.bb_instructions ==>
  ~MEM v (inst_defs (EL k bb.bb_instructions))
Proof
  simp[current_changing_site_def, inst_defs_def] >> rpt strip_tac >>
  metis_tac[lookup_block_MEM, lookup_block_label, MEM_EL]
QED

Theorem current_non_site_cut_clear:
  ~current_changing_site fn ins v l ==> current_phi_cut_clear fn v l
Proof
  simp[current_phi_cut_clear_def] >> rpt strip_tac >>
  `k < LENGTH bb.bb_instructions` by
    metis_tac[current_collect_phis_length, LESS_LESS_EQ_TRANS] >>
  metis_tac[current_non_site_outputs]
QED

Theorem current_non_site_live_edge:
  wf_function fn /\ fn_cfg_edge fn a b /\
  ~current_changing_site fn ins v a /\ current_phi_cut_clear fn v b /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  current_live_route_edge fn v a b
Proof
  strip_tac >>
  `MEM a (fn_labels fn) /\ MEM b (fn_labels fn)` by
    metis_tac[current_cfg_edge_succs, current_cfg_edge_preds,
      cfg_analyze_succ_labels, cfg_analyze_pred_labels] >>
  `?ab. lookup_block a fn.fn_blocks = SOME ab` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  `?bb. lookup_block b fn.fn_blocks = SOME bb` by
    (gvs[fn_labels_def, MEM_MAP] >>
     metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def]) >>
  simp[current_live_route_edge_def] >> conj_tac
  >- metis_tac[current_non_site_outputs] >>
  conj_tac >- metis_tac[current_phi_cut_clear_def] >>
  metis_tac[lookup_block_MEM]
QED

Theorem current_non_site_live_route:
  !ls a b. wf_function fn /\ LRC (fn_cfg_edge fn) ls a b /\
  EVERY (\l. ~current_changing_site fn ins v l) ls /\
  current_phi_cut_clear fn v b /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) ==>
  LRC (current_live_route_edge fn v) ls a b
Proof
  Induct >> simp[LRC_def] >> rpt strip_tac >> gvs[] >>
  qexists_tac `z` >> conj_tac
  >- (`current_phi_cut_clear fn v z` by
        (Cases_on `ls` >> gvs[LRC_def] >>
         metis_tac[current_non_site_cut_clear]) >>
      metis_tac[current_non_site_live_edge]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem current_last_site_route_dominates:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME eb /\ MEM d (fn_labels fn) /\
  current_changing_site fn ins v d /\
  LRC (fn_cfg_edge fn) ls d b /\ ls <> [] /\
  EVERY (\l. ~current_changing_site fn ins v l) (TL ls) /\
  ~ins v b /\ current_phi_cut_clear fn v b /\
  (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
    (liveness_analyze fn) fn) b = SOME vs /\ MEM v vs) /\
  (!pb phi. MEM pb fn.fn_blocks /\
    MEM phi (collect_phis pb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs phi.inst_operands))) /\
  (!x y. current_changing_site fn ins v x /\
    MEM y (frontier_of (dom_analyze (cfg_analyze fn) fn) x) /\
    (?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) y = SOME vs /\ MEM v vs) ==> ins v y) ==>
  strict_dominates (dom_analyze (cfg_analyze fn) fn) d b
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule_all current_route_frontier_crossing >> strip_tac >>
  `EVERY (\l. ~current_changing_site fn ins v l) post` by
    (Cases_on `pre` >> gvs[]) >>
  `LRC (current_live_route_edge fn v) post y b` by
    metis_tac[current_non_site_live_route] >>
  `?vs. ALOOKUP (select_current_live_in (blocks_have_leading_phi fn.fn_blocks)
      (liveness_analyze fn) fn) y = SOME vs /\ MEM v vs` by
    metis_tac[current_selected_live_route] >>
  `MEM y (frontier_of (dom_analyze (cfg_analyze fn) fn) d)` by
    gvs[ALOOKUP_current_frontier_map] >>
  `ins v y` by metis_tac[] >>
  Cases_on `post` >> gvs[LRC_def, current_changing_site_def]
QED
