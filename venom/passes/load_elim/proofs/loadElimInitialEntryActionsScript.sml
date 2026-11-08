Theory loadElimInitialEntryActions
Ancestors
  loadElimJoinPlacement loadElimOriginHelpers loadElimPhiCapture
  loadElimReachableBoundary loadElimDefs venomInst cfgDefs cfgAnalysisProps venomWf list pred_set finite_map

Theorem le_boundary_find_join_nonentry:
  !cfg visited lbl. cfg = cfg_analyze fn ==>
  !bb ops. wf_function fn /\ MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
    FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) lbl)) k = SOME ops /\
    MEM a ops /\ MEM b ops /\ a <> b /\
    (!l. l IN visited ==> fn_entry_label fn <> SOME l) ==>
    fn_entry_label fn <> SOME (find_join_block cfg visited lbl)
Proof
  recInduct find_join_block_ind >> rpt gen_tac >> disch_then (mk_asm "ih") >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  DISCH_THEN STRIP_ASSUME_TAC >> gvs[] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    metis_tac[le_two_distinct_boundary_nonentry] >>
  Cases_on `bb.bb_label IN visited`
  >- simp[Once find_join_block_def] >>
  Cases_on `?pred. cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred]`
  >- (pop_assum strip_assume_tac >>
      `le_fold_preserves ctx bb.bb_instructions k` by
        metis_tac[le_two_distinct_boundary_preserves] >>
      drule_all le_analyze_boundary_preserving_reverse >> strip_tac >>
      `MEM pred (fn_labels fn)` by
        metis_tac[cfg_analyze_pred_labels, MEM] >>
      fs[fn_labels_def, MEM_MAP] >>
      `find_join_block (cfg_analyze fn) visited bb.bb_label =
       find_join_block (cfg_analyze fn) (bb.bb_label INSERT visited) pred` by
        simp[Once find_join_block_def] >>
      pop_assum (fn th => pure_rewrite_tac[th]) >>
      asm "ih" irule >>
      simp[] >> metis_tac[SUBSET_DEF]) >>
  `find_join_block (cfg_analyze fn) visited bb.bb_label = bb.bb_label` by
    (simp[Once find_join_block_def] >>
     Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> simp[] >>
     Cases_on `t` >> gvs[]) >>
  metis_tac[]
QED
