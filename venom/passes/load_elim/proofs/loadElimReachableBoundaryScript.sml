Theory loadElimReachableBoundary
Ancestors
  loadElimBoundaryProvenance loadElimConvergence loadElimSolverHelpers
  loadElimDefs dfAnalyzeDefs worklistDefs worklistProofs latticeDefs
  cfgAnalysisProps cfgDefs venomWf venomInst finite_map pred_set list relation

Definition le_boundary_reachable_def:
  le_boundary_reachable fn st <=>
    !lbl. ~MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
      df_boundary NONE st lbl = NONE
End

Theorem le_entry_preorder:
  fn_entry_label fn = SOME lbl ==> MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  simp[fn_entry_label_def] >> Cases_on `entry_block fn` >> simp[] >>
  strip_tac >> gvs[] >> drule cfg_analyze_preorder_entry_first >>
  strip_tac >> Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> gvs[]
QED

Theorem le_preorder_successors:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
  EVERY (\l. MEM l (cfg_analyze fn).cfg_dfs_pre)
    (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  strip_tac >>
  `?bb. entry_block fn = SOME bb` by
    (Cases_on `fn.fn_blocks` >>
     fs[wf_function_def, fn_has_entry_def, entry_block_def]) >>
  drule cfg_analyze_reachable_sets >> strip_tac >>
  drule_all cfg_analyze_semantic_reachability >> strip_tac >>
  fs[EXTENSION] >> simp[EVERY_MEM] >> rpt strip_tac >>
  `cfg_path (cfg_analyze fn) bb.bb_label lbl` by metis_tac[] >>
  `cfg_path (cfg_analyze fn) bb.bb_label l` by
    (pure_rewrite_tac[cfg_path_def] >>
     irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >>
     qexists `lbl` >> simp[GSYM cfg_path_def]) >>
  metis_tac[]
QED

Theorem le_boundary_reachable_init:
  le_boundary_reachable fn
    (case fn_entry_label fn of
       NONE => init_df_state NONE (fn_labels fn)
     | SOME lbl => (init_df_state NONE (fn_labels fn)) with
         ds_boundary := (init_df_state NONE (fn_labels fn)).ds_boundary |+
           (lbl, SOME FEMPTY))
Proof
  Cases_on `fn_entry_label fn`
  >- simp[le_boundary_reachable_def, le_init_boundary_none] >>
  simp[le_boundary_reachable_def] >> rpt strip_tac >>
  `lbl <> x` by metis_tac[le_entry_preorder] >>
  simp[df_boundary_def, FLOOKUP_UPDATE] >>
  pure_once_rewrite_tac[GSYM df_boundary_def] >>
  MATCH_ACCEPT_TAC le_init_boundary_none
QED

Theorem le_boundary_reachable_process:
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\ le_boundary_reachable fn st ==>
  le_boundary_reachable fn (le_solver_process ctx fn lbl st)
Proof
  simp[le_boundary_reachable_def, le_process_boundary] >> metis_tac[]
QED

Theorem le_solver_iterate_reachable:
  wf_function fn ==>
  (\st. le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
           (le_generated_operands (fn_insts fn)) st /\
         le_boundary_reachable fn st)
    (SND (wl_iterate
      (\lbl old new. df_boundary NONE new lbl <> df_boundary NONE old lbl)
      (le_solver_process ctx fn) (cfg_succs_of (cfg_analyze fn))
      (cfg_analyze fn).cfg_dfs_pre
      (case fn_entry_label fn of
         NONE => init_df_state NONE (fn_labels fn)
       | SOME lbl => (init_df_state NONE (fn_labels fn)) with
           ds_boundary := (init_df_state NONE (fn_labels fn)).ds_boundary |+
             (lbl, SOME FEMPTY))))
Proof
  strip_tac >> irule wl_iterate_invariant_process_restricted >>
  simp[le_solver_entry_init, le_boundary_reachable_init, le_process_changed] >>
  qexistsl [
    `CARD (set (fn_labels fn)) *
      (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
        (CARD (le_generated_operands (fn_insts fn)) + 1))`,
    `le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
      (le_generated_operands (fn_insts fn))`,
    `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre`] >>
  simp[le_process_changed, le_solver_entry_init, le_boundary_reachable_init,
       EVERY_MEM, le_preorder_successors] >>
  metis_tac[arithmeticTheory.ADD_COMM, le_solver_rank_bound, FINITE_LIST_TO_SET,
    loadElimSupportHelpersTheory.le_generated_operands_finite,
    loadElimSupportHelpersTheory.le_generated_keys_finite,
    le_solver_premises, le_solver_rank_strict, le_boundary_reachable_process]
QED

Theorem le_boundary_reachable_populate:
  le_boundary_reachable fn
    (df_populate_inst dir bottom join transfer edge ctx entry cfg bbs lbls st) <=>
  le_boundary_reachable fn st
Proof
  simp[le_boundary_reachable_def, df_boundary_def, le_populate_boundary]
QED

Theorem le_analyze_boundary_unvisited:
  wf_function fn /\ ~MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
  df_boundary NONE (load_analyze ctx fn) lbl = NONE
Proof
  strip_tac >> drule le_solver_iterate_reachable >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `le_boundary_reachable _ _` mp_tac >>
  simp[load_analyze_def, df_analyze_def, le_solver_process_def] >>
  Cases_on `fn_entry_label fn` >>
  simp[fn_labels_def, le_boundary_reachable_def, df_boundary_def,
       le_populate_boundary]
QED

Theorem le_analyze_lookup_reachable:
  wf_function fn /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) lbl)) k = SOME xs ==>
  MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> CCONTR_TAC >>
  `df_boundary NONE (load_analyze ctx fn) lbl = NONE` by
    metis_tac[le_analyze_boundary_unvisited] >>
  gvs[unwrap_load_lattice_def]
QED
