Theory loadElimInitialEntryActions
Ancestors cfgCorrectnessProof
  loadElimAllBlockPopulation loadElimConvergence loadElimSupportHelpers
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

Theorem le_point_multivalue_nonentry:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME ops /\
  1 < LENGTH ops ==>
  fn_entry_label fn <> SOME lbl
Proof
  strip_tac >> drule_all le_analyze_all_block_multivalue_origin >> strip_tac >>
  metis_tac[loadElimBoundaryProvenanceTheory.le_joined_entry_missing, optionTheory.NOT_NONE_SOME]
QED

Theorem le_point_find_join_nonentry:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME ops /\
  1 < LENGTH ops ==>
  fn_entry_label fn <> SOME (find_join_block (cfg_analyze fn) {} lbl)
Proof
  strip_tac >>
  `fn_entry_label fn <> SOME lbl` by metis_tac[le_point_multivalue_nonentry] >>
  drule_all le_analyze_all_block_multivalue_origin >> strip_tac >>
  Cases_on `?p. cfg_preds_of (cfg_analyze fn) lbl = [p]`
  >- (pop_assum strip_assume_tac >>
      `FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) p)) k = SOME ops` by
        metis_tac[loadElimBoundaryProvenanceTheory.le_joined_sole_pred] >>
      `ALL_DISTINCT ops` by
        metis_tac[le_analyze_boundary_supported, le_lattice_supported_def] >>
      Cases_on `ops` >> gvs[] >> Cases_on `t` >> gvs[] >>
      `MEM p (fn_labels fn)` by metis_tac[cfg_analyze_pred_labels, MEM] >>
      fs[fn_labels_def, MEM_MAP] >>
      simp[Once find_join_block_def] >>
      irule le_boundary_find_join_nonentry >> simp[] >> gvs[] >> metis_tac[MEM]) >>
  `find_join_block (cfg_analyze fn) {} lbl = lbl` by
    (simp[Once find_join_block_def] >>
     Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> simp[] >>
     Cases_on `t` >> gvs[]) >> simp[]
QED

Theorem le_collected_action_nonentry:
  wf_function fn /\
  MEM pa (collect_phi_actions max_id ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ==>
  fn_entry_label fn <> SOME pa.pa_join_lbl
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >> gvs[] >>
  irule le_point_find_join_nonentry >>
  simp[] >> qexistsl [`bb`, `ctx`,
    `load_get_read_key ctx.lctx_bp ctx.lctx_addr_space (normalize_operand ctx.lctx_dfg []) (EL idx bb.bb_instructions)`, `idx`, `vs`] >>
  simp[] >> irule venomExecPropsTheory.MEM_lookup_block >> simp[] >>
  fs[wf_function_def, fn_labels_def]
QED

Theorem le_entry_phis_empty:
  wf_function fn /\ fn_entry_label fn = SOME lbl ==>
  phis_for_block
    (collect_phi_actions max_id ctx (cfg_analyze fn) (load_analyze ctx fn) fn) lbl = []
Proof
  strip_tac >> simp[phis_for_block_def, FILTER_EQ_NIL, EVERY_MEM] >>
  metis_tac[le_collected_action_nonentry]
QED
