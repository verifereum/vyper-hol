(* Current-analysis adapters used by the supply-aware SSA proof. *)
Theory makeSsaCurrentAnalysis
Ancestors
  makeSsaCurrentDefs makeSsaDefs cfgAnalysisProps cfgHelpers dominatorProofs
  dominatorQueryProofs dominatorRankProofs makeSsaCurrentTree dominatorDefs
  venomWf cfgWf cfgDefs venomInst venomExecProps relation list sorting cfgCorrectnessProof

Theorem current_cfg_edge_succs:
  wf_function fn ==>
  (fn_cfg_edge fn a b <=> MEM b (cfg_succs_of (cfg_analyze fn) a))
Proof
  strip_tac >> eq_tac
  >- (rw[fn_cfg_edge_def] >>
      drule_all cfg_analyze_preserves_bb_succs >> simp[]) >>
  strip_tac >>
  `MEM a (fn_labels fn)` by
    (spose_not_then assume_tac >>
     gvs[cfg_analyze_succs, fn_labels_def, cfg_succs_of_not_in_labels]) >>
  gvs[fn_labels_def, MEM_MAP] >>
  drule_all cfg_analyze_preserves_bb_succs >> strip_tac >>
  simp[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem current_cfg_edge_preds:
  wf_function fn ==>
  (fn_cfg_edge fn a b <=> MEM a (cfg_preds_of (cfg_analyze fn) b))
Proof
  simp[current_cfg_edge_succs, GSYM cfg_edge_symmetry_uncond]
QED

Theorem current_succ_query_edge:
  wf_function fn /\ MEM a (fn_labels fn) ==>
  (MEM b (THE (ALOOKUP (current_succ_map fn) a)) <=> fn_cfg_edge fn a b)
Proof
  simp[ALOOKUP_current_succ_map, current_cfg_edge_succs]
QED

Theorem current_pred_query_edge:
  wf_function fn /\ MEM b (fn_labels fn) ==>
  (MEM a (THE (ALOOKUP (current_pred_map fn) b)) <=> fn_cfg_edge fn a b)
Proof
  simp[ALOOKUP_current_pred_map, current_cfg_edge_preds]
QED

Theorem current_cfg_path:
  wf_function fn ==>
  cfgDefs$cfg_path (cfg_analyze fn) = RTC (fn_cfg_edge fn)
Proof
  strip_tac >>
  `fn_cfg_edge fn = (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))` by
    simp[FUN_EQ_THM, current_cfg_edge_succs] >>
  simp[cfgDefsTheory.cfg_path_def]
QED

Theorem current_cfg_reachable:
  wf_function fn ==>
  (cfg_reachable_of (cfg_analyze fn) lbl <=> fn_reachable fn lbl)
Proof
  strip_tac >> Cases_on `entry_block fn`
  >- (gvs[entry_block_def, NULL_EQ, cfg_analyze_def, fn_reachable_def,
          fn_entry_label_def, cfg_reachable_of_def,
          fmap_lookup_list_def, build_reachable_def]) >>
  drule_all cfg_analyze_semantic_reachability >>
  simp[current_cfg_path, fn_reachable_def, fn_entry_label_def]
QED

Theorem current_all_labels_reachable:
  wf_function fn /\ all_reachable fn /\ MEM lbl (fn_labels fn) ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  simp[current_cfg_reachable] >>
  rw[all_reachable_def, fn_labels_def, MEM_MAP] >> metis_tac[]
QED

Theorem current_dom_child_reachable:
  wf_function fn /\ all_reachable fn /\
  MEM c (dominated_of (dom_analyze (cfg_analyze fn) fn) n) ==>
  cfg_reachable_of (cfg_analyze fn) c
Proof
  rw[dominated_query_membership] >>
  irule current_all_labels_reachable >> simp[]
QED

Theorem current_dom_child_strict:
  wf_function fn /\ all_reachable fn /\
  MEM c (dominated_of (dom_analyze (cfg_analyze fn) fn) n) ==>
  strict_dominates (dom_analyze (cfg_analyze fn) fn) n c
Proof
  rpt strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) c` by
    (irule current_dom_child_reachable >> metis_tac[]) >>
  gvs[dominated_query_membership] >>
  metis_tac[idom_is_immediate]
QED

Theorem current_dom_child_rank:
  wf_function fn /\ all_reachable fn /\ MEM n (fn_labels fn) /\
  current_tree_edge (dom_analyze (cfg_analyze fn) fn) n c ==>
  MEM c (fn_labels fn) /\ dominator_query_rank fn n < dominator_query_rank fn c
Proof
  simp[current_tree_edge_def] >> strip_tac >>
  `MEM c (fn_labels fn)` by metis_tac[dominated_query_membership] >>
  simp[] >> irule dominator_query_rank_strict >> simp[] >>
  metis_tac[current_all_labels_reachable, current_dom_child_strict]
QED

Theorem current_dom_parent_exists:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  MEM z (fn_labels fn) /\ z <> bb.bb_label ==>
  ?p. MEM p (fn_labels fn) /\
    current_tree_edge (dom_analyze (cfg_analyze fn) fn) p z
Proof
  rpt strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) z` by metis_tac[current_all_labels_reachable] >>
  `?p. idom_of (dom_analyze (cfg_analyze fn) fn) z = SOME p` by
    metis_tac[idom_exists] >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) p z` by
    metis_tac[idom_is_immediate] >>
  `MEM p (fn_labels fn)` by
    (gvs[strict_dominates_def, dominates_def] >> metis_tac[dom_labels_bounded]) >>
  qexists_tac `p` >> simp[current_tree_edge_def, dominated_query_membership]
QED

Theorem current_dom_aux_postorder_perm:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb ==>
  PERM (dom_tree_postorder (current_dom_tree_aux
    (dom_analyze (cfg_analyze fn) fn) (LENGTH (fn_labels fn)) bb.bb_label))
    (fn_labels fn)
Proof
  strip_tac >> irule current_tree_postorder_perm >>
  conj_tac
  >- (rpt strip_tac >> gvs[current_tree_edge_def, dominated_query_membership]) >>
  conj_tac >- metis_tac[current_dom_parent_exists] >>
  conj_tac >- simp[dominated_query_distinct] >>
  conj_tac
  >- (qexists_tac `dominator_query_rank fn` >>
      metis_tac[current_dom_child_rank, dominator_query_rank_bound]) >>
  conj_tac >- gvs[wf_function_def] >>
  gvs[entry_block_def, fn_labels_def, AllCaseEqs()] >>
  Cases_on `fn.fn_blocks` >> gvs[]
QED

Theorem current_dom_postorder_perm:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb ==>
  PERM (current_dom_postorder fn) (fn_labels fn)
Proof
  strip_tac >>
  `fn_entry_label fn = SOME bb.bb_label` by simp[fn_entry_label_def] >>
  simp[current_dom_postorder_def, current_dom_tree_def] >>
  metis_tac[current_dom_aux_postorder_perm]
QED

Theorem current_dom_root_fuel_stable:
  wf_function fn /\ all_reachable fn /\ MEM root (fn_labels fn) ==>
  !extra. current_dom_tree_aux (dom_analyze (cfg_analyze fn) fn)
    (LENGTH (fn_labels fn)) root =
    current_dom_tree_aux (dom_analyze (cfg_analyze fn) fn)
    (LENGTH (fn_labels fn) + extra) root
Proof
  strip_tac >> irule current_tree_root_fuel_stable >>
  simp[] >> qexists_tac `dominator_query_rank fn` >>
  metis_tac[current_dom_child_rank, dominator_query_rank_bound]
QED

Theorem current_frontier_query_correct:
  wf_function fn /\ MEM n (fn_labels fn) /\
  cfg_reachable_of (cfg_analyze fn) n /\
  cfg_reachable_of (cfg_analyze fn) y /\
  LENGTH (cfg_preds_of (cfg_analyze fn) y) > 1 /\
  fn_entry_label fn <> SOME y /\
  (!p. MEM p (cfg_preds_of (cfg_analyze fn) y) ==>
       cfg_reachable_of (cfg_analyze fn) p) ==>
  (MEM y (THE (ALOOKUP (current_frontier_map fn) n)) <=>
   ?p. MEM p (cfg_preds_of (cfg_analyze fn) y) /\
       dominates (dom_analyze (cfg_analyze fn) fn) n p /\
       ~strict_dominates (dom_analyze (cfg_analyze fn) fn) n y)
Proof
  strip_tac >> simp[ALOOKUP_current_frontier_map] >>
  metis_tac[dom_frontier_correct]
QED

Theorem lookup_block_labels_identity:
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
  MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl bbs) (MAP (\b. b.bb_label) bbs))) = bbs
Proof
  strip_tac >>
  `MAP (\lbl. lookup_block lbl bbs) (MAP (\b. b.bb_label) bbs) = MAP SOME bbs` by
    (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >> simp[] >>
     rpt strip_tac >> irule MEM_lookup_block >> simp[]) >>
  simp[] >> pop_assum kall_tac >> pop_assum kall_tac >>
  Induct_on `bbs` >> simp[]
QED

Theorem lookup_block_labels_perm:
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
  PERM labels (MAP (\b. b.bb_label) bbs) ==>
  PERM (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl bbs) labels))) bbs
Proof
  strip_tac >>
  `PERM (MAP (\lbl. lookup_block lbl bbs) labels)
    (MAP (\lbl. lookup_block lbl bbs) (MAP (\b. b.bb_label) bbs))` by
    metis_tac[PERM_MAP] >>
  drule PERM_FILTER >> disch_then (qspec_then `IS_SOME` mp_tac) >>
  strip_tac >>
  `bbs = MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl bbs) (MAP (\b. b.bb_label) bbs)))` by
    metis_tac[lookup_block_labels_identity] >>
  metis_tac[PERM_MAP]
QED

Theorem current_ordered_blocks_perm:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb ==>
  PERM (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))
    fn.fn_blocks
Proof
  strip_tac >> irule lookup_block_labels_perm >>
  conj_tac >- gvs[wf_function_def, fn_labels_def] >>
  metis_tac[current_dom_postorder_perm, fn_labels_def]
QED

Theorem current_compute_defs_complete:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb /\
  MEM b fn.fn_blocks /\ MEM v (block_assignments b) ==>
  ?dbs. ALOOKUP (compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn))))) v = SOME dbs /\
    MEM b.bb_label dbs
Proof
  strip_tac >> irule compute_defs_complete >> simp[] >>
  drule_all current_ordered_blocks_perm >> metis_tac[PERM_MEM_EQ]
QED

Theorem current_compute_defs_keys:
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME bb ==>
  (MEM v (MAP FST (compute_defs (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) (current_dom_postorder fn)))))) <=>
   MEM v (FLAT (MAP block_assignments fn.fn_blocks)))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `compute_defs ordered` >>
  `PERM ordered fn.fn_blocks` by
    (simp[Abbr `ordered`] >> metis_tac[current_ordered_blocks_perm]) >>
  simp[compute_defs_keys, MEM_FLAT, MEM_MAP] >>
  metis_tac[PERM_MEM_EQ]
QED
