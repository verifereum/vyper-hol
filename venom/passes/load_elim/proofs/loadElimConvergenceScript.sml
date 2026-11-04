Theory loadElimConvergence
Ancestors
  loadElimDefs loadElimSupportHelpers loadElimOrderHelpers loadElimSolverHelpers
  dfAnalyzeDefs dfAnalyzeProofs cfgAnalysisProps worklistDefs
  venomInst finite_map pred_set list

Theorem le_solver_entry_init:
  wf_function fn ==>
  le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn))
    (case fn_entry_label fn of
       NONE => init_df_state NONE (fn_labels fn)
     | SOME lbl => (init_df_state NONE (fn_labels fn)) with
         ds_boundary := (init_df_state NONE (fn_labels fn)).ds_boundary |+
           (lbl, SOME FEMPTY))
Proof
  strip_tac >> Cases_on `fn_entry_label fn` >- simp[le_solver_init] >>
  `MEM x (fn_labels fn)` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, fn_labels_def]) >>
  `le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
    (le_generated_operands (fn_insts fn)) (init_df_state NONE (fn_labels fn))`
    by irule le_solver_init >>
  fs[le_solver_inv_def] >>
  simp[le_solver_inv_def, EXTENSION, FLOOKUP_UPDATE] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> Cases_on `x = lbl` >> gvs[] >> metis_tac[]
QED

Theorem le_solver_deps_complete:
  wf_function fn ==>
  wl_deps_complete
    (\lbl old new. df_boundary NONE new lbl <> df_boundary NONE old lbl)
    (le_solver_process ctx fn) (cfg_succs_of (cfg_analyze fn))
Proof
  strip_tac >> simp[le_solver_process_def] >>
  irule (SRULE [LET_THM] (Q.SPEC `Forward` df_process_deps_complete_proof)) >>
  simp[cfg_edge_symmetry_uncond, le_join_absorption]
QED
