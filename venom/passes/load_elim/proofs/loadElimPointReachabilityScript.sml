Theory loadElimPointReachability
Ancestors
  loadElimReachableBoundary loadElimTransferProvenance loadElimConvergence
  loadElimDefs cfgAnalysisProps cfgDefs dfAnalyzeDefs venomWf venomInst
  finite_map list pred_set

Theorem le_unvisited_joined_input:
  wf_function fn /\ ~MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
  df_joined_val Forward NONE load_join load_edge_transfer ctx
    (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) (load_analyze ctx fn) lbl = NONE
Proof
  strip_tac >>
  `!p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) ==>
       ~MEM p (cfg_analyze fn).cfg_dfs_pre` by
    (rpt strip_tac >> drule_all le_preorder_successors >>
     simp[EVERY_MEM, EXISTS_MEM] >> metis_tac[cfg_edge_symmetry_uncond]) >>
  `MAP (\p. load_edge_transfer ctx p lbl
     (df_boundary NONE (load_analyze ctx fn) p))
     (cfg_preds_of (cfg_analyze fn) lbl) =
     MAP (\p. NONE) (cfg_preds_of (cfg_analyze fn) lbl)` by
    (irule MAP_CONG >> simp[load_edge_transfer_def] >>
     metis_tac[le_analyze_boundary_unvisited]) >>
  `!ps:string list. FOLDL load_join NONE (MAP (\p. NONE) ps) = NONE` by
    (Induct >> simp[load_join_def]) >>
  `fn_entry_label fn <> SOME lbl` by metis_tac[le_entry_preorder] >>
  Cases_on `fn_entry_label fn` >>
  simp[df_joined_val_def] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[load_edge_transfer_def, load_join_def]
QED
