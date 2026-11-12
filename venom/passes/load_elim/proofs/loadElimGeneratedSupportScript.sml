Theory loadElimGeneratedSupport
Ancestors
  loadElimSolverProvenance loadElimConvergence loadElimSolverHelpers
  loadElimSupportHelpers loadElimDefs dfAnalyzeDefs cfgAnalysisProps
  venomInst livenessTransferProofs list rich_list

Theorem le_analyze_entry_supported:
  wf_function fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  le_lattice_supported (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn))
    (df_at NONE (load_analyze ctx fn) lbl 0)
Proof
  strip_tac >> drule_all le_analyze_entry_join >>
  disch_then (qspec_then `ctx` SUBST1_TAC) >>
  irule le_boundary_joined_supported >>
  metis_tac[le_analyze_boundary_supported]
QED

Theorem le_analyze_point_supported:
  wf_function fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions ==>
  le_lattice_supported (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn))
    (df_at NONE (load_analyze ctx fn) lbl n)
Proof
  strip_tac >>
  `is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn)` by
    metis_tac[le_load_analyze_fixpoint, le_solver_process_def] >>
  drule_all le_analyze_prefix_fold >> disch_then SUBST1_TAC >>
  irule le_transfer_fold_supported >> conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      `MEM i bb.bb_instructions` by metis_tac[MEM_TAKE] >>
      `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
      `!bbs. MEM bb bbs ==> MEM i (fn_insts_blocks bbs)` by
        (Induct >> simp[fn_insts_blocks_def] >> metis_tac[]) >>
      simp[fn_insts_def]) >>
  metis_tac[le_analyze_entry_supported]
QED
