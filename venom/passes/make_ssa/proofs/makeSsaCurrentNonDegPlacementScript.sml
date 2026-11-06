Theory makeSsaCurrentNonDegPlacement
Ancestors
  makeSsaCurrentPlacement makeSsaCurrentPlacementCut makeSsaCurrentDefSupport
  makeSsaCurrentAnalysis makeSsaCurrentFrontier makeSsaCurrentDefs alist list sorting

(* A recursive self-frontier cannot be the first cause of reachability. *)
Theorem current_pruned_reach_nonself_source:
  current_pruned_reach df li v roots y ==>
  ?d. current_frontier_edge df d y /\
      (MEM d roots \/ (d <> y /\ current_pruned_reach df li v roots d))
Proof
  qid_spec_tac `y` >>
  ho_match_mp_tac current_pruned_reach_strongind >>
  conj_tac
  >- (rpt strip_tac >> qexists_tac `d` >> simp[]) >>
  map_every qx_gen_tac [`source`, `target`] >>
  disch_tac >> Cases_on `source = target`
  >- (gvs[] >> metis_tac[]) >>
  qexists_tac `source` >> gvs[]
QED

Theorem current_actual_inserted_nonself_source:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME entry /\
  current_actual_inserted fn v y ==>
  ?d. current_frontier_edge (current_frontier_map fn) d y /\
      ((?bb inst. MEM bb fn.fn_blocks /\ bb.bb_label = d /\
          MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) \/
       (d <> y /\ current_actual_inserted fn v d))
Proof
  strip_tac >> drule_all current_ordered_blocks_perm >> strip_tac >>
  qpat_x_assum `current_actual_inserted _ _ _` mp_tac >>
  simp[current_actual_inserted_def] >> strip_tac >>
  drule current_pruned_reach_nonself_source >> strip_tac
  >- (drule_all compute_defs_support >> strip_tac >>
      qexists_tac `d` >> simp[] >> disj1_tac >>
      qexistsl_tac [`bb`, `inst`] >> simp[] >>
      metis_tac[PERM_MEM_EQ]) >>
  qexists_tac `d` >> simp[current_actual_inserted_def] >>
  disj2_tac >> goal_assum $ drule_at Any
QED

Theorem nondeg_lrc_first_arrival:
  !ls start target. LRC R ls start target /\ start <> target ==>
  ?pre q. LRC R pre start q /\ R q target /\ q <> target /\
          ~MEM target pre /\ set (pre ++ [q]) SUBSET set ls
Proof
  Induct >> simp[listTheory.LRC_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `z = target`
  >- (qexistsl_tac [`[]`, `h`] >> gvs[listTheory.LRC_def]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`h::pre`, `q`] >>
  simp[listTheory.LRC_def] >>
  gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem nondeg_separating_predecessor:
  wf_function fn /\ entry_block fn = SOME entry /\
  cfg_reachable_of (cfg_analyze fn) y /\ y <> entry.bb_label /\
  MEM d (fn_labels fn) /\
  (d = y \/ ~dominates (dom_analyze (cfg_analyze fn) fn) d y) ==>
  ?q. MEM q (cfg_preds_of (cfg_analyze fn) y) /\
      ~dominates (dom_analyze (cfg_analyze fn) fn) d q /\
      ~dominates (dom_analyze (cfg_analyze fn) fn) y q
Proof
  rpt gen_tac >> disch_tac >> Cases_on `d = y`
  >- (gvs[] >> drule_all dominatorProofsTheory.exists_pred_not_dominated >>
      metis_tac[]) >>
  gvs[] >>
  `?ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
      ls entry.bb_label y /\ ~MEM d ls` by
    (spose_not_then assume_tac >>
     `dominates (dom_analyze (cfg_analyze fn) fn) d y` suffices_by gvs[] >>
     pure_rewrite_tac[dominatorDefsTheory.dominates_def] >>
     irule dominatorProofsTheory.on_every_path_dom >>
     goal_assum $ drule_at Any >> gvs[] >> metis_tac[]) >>
  `entry.bb_label <> y` by simp[] >>
  drule_all nondeg_lrc_first_arrival >> strip_tac >>
  `~MEM d pre /\ d <> q` by
    (gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  qexists_tac `q` >> conj_tac
  >- metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  qspecl_then [`fn`, `entry`, `pre`, `q`] mp_tac
    dominatorProofsTheory.dom_on_every_path >>
  simp[GSYM dominatorDefsTheory.dominates_def] >> metis_tac[]
QED

Theorem current_nondeg_frontier_source_label:
  current_frontier_edge (current_frontier_map fn) d y ==>
  MEM d (fn_labels fn)
Proof
  simp[current_frontier_edge_def] >> strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[current_frontier_map_def, current_query_map_def, MEM_MAP] >> metis_tac[]
QED

Theorem current_nondeg_frontier_nonentry:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  current_frontier_edge (current_frontier_map fn) d y ==>
  fn_entry_label fn <> SOME y
Proof
  strip_tac >>
  drule current_nondeg_frontier_source_label >> strip_tac >>
  gvs[current_frontier_edge_def] >>
  drule_all current_frontier_target_support >> simp[]
QED

Theorem nondeg_inserted_graph_witnesses:
  wf_function fn /\ all_reachable fn /\ first_block_no_preds fn /\
  entry_block fn = SOME entry /\ current_actual_inserted fn v y ==>
  ?d p q. current_frontier_edge (current_frontier_map fn) d y /\
    ((?bb inst. MEM bb fn.fn_blocks /\ bb.bb_label = d /\
      MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs) \/
      (d <> y /\ current_actual_inserted fn v d)) /\
    MEM p (cfg_preds_of (cfg_analyze fn) y) /\
    MEM q (cfg_preds_of (cfg_analyze fn) y) /\
    dominates (dom_analyze (cfg_analyze fn) fn) d p /\
    ~dominates (dom_analyze (cfg_analyze fn) fn) d q /\
    ~dominates (dom_analyze (cfg_analyze fn) fn) y q /\ p <> q
Proof
  strip_tac >> drule_all current_actual_inserted_nonself_source >>
  disch_then (qx_choose_then `d` strip_assume_tac) >>
  `MEM d (fn_labels fn)` by metis_tac[current_nondeg_frontier_source_label] >>
  `MEM y (fn_labels fn)` by metis_tac[current_frontier_edge_target_label] >>
  `fn_entry_label fn <> SOME y` by metis_tac[current_nondeg_frontier_nonentry] >>
  `y <> entry.bb_label` by
    gvs[venomInstTheory.entry_block_def, venomInstTheory.fn_entry_label_def,
        AllCaseEqs()] >>
  `cfg_reachable_of (cfg_analyze fn) y` by
    (gvs[current_cfg_reachable, venomInstTheory.fn_labels_def, MEM_MAP,
         cfgWfTheory.all_reachable_def] >> metis_tac[]) >>
  `?p. MEM p (cfg_preds_of (cfg_analyze fn) y) /\
    dominates (dom_analyze (cfg_analyze fn) fn) d p /\
    ~strict_dominates (dom_analyze (cfg_analyze fn) fn) d y` by
    (gvs[current_frontier_edge_def] >> metis_tac[current_frontier_elim]) >>
  `d = y \/ ~dominates (dom_analyze (cfg_analyze fn) fn) d y` by
    (gvs[dominatorDefsTheory.strict_dominates_def] >> metis_tac[]) >>
  `?q. MEM q (cfg_preds_of (cfg_analyze fn) y) /\
    ~dominates (dom_analyze (cfg_analyze fn) fn) d q /\
    ~dominates (dom_analyze (cfg_analyze fn) fn) y q` by
    metis_tac[nondeg_separating_predecessor] >>
  qexistsl_tac [`d`, `p`, `q`] >> simp[] >> metis_tac[]
QED
