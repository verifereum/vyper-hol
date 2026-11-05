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
  FAIL_TAC "closure"
QED
