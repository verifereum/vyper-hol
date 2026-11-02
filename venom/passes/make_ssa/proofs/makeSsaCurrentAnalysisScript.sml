(* Current-analysis adapters used by the supply-aware SSA proof. *)
Theory makeSsaCurrentAnalysis
Ancestors
  makeSsaCurrentDefs cfgAnalysisProps cfgHelpers dominatorAnalysisProps
  venomWf cfgWf cfgDefs venomInst relation list

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
