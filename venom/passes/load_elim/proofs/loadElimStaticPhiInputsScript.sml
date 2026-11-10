Theory loadElimStaticPhiInputs
Ancestors
  loadElimStaticAvailability loadElimActualGeneration loadElimReachableBoundary
  loadElimConvergence loadElimSolverHelpers loadElimPhiCapture loadElimOriginHelpers
  loadElimDefs codegenReadyCompute cfgAnalysisProps cfgDefs loadElimReachableSSA
  venomWf venomInst venomExecProofs dfAnalyzeDefs list pair finite_map pred_set

Theorem le_static_boundary_singleton_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ MEM pb fn.fn_blocks /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) pb.bb_label)) key = SOME [Var v] ==>
  def_available_at fn pb NONE v
Proof
  strip_tac >>
  `MEM pb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_analyze_lookup_reachable] >>
  `fn_reachable fn pb.bb_label` by
    (drule cfg_analyze_reachable_sets >>
     simp[EXTENSION] >> metis_tac[fn_reachable_cfg_analyze]) >>
  `lookup_block pb.bb_label fn.fn_blocks = SOME pb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn)` by
    metis_tac[le_load_analyze_fixpoint, le_solver_process_def] >>
  drule_all le_analyze_singleton_exit >> strip_tac >>
  irule le_static_singleton_endpoint_available >> metis_tac[]
QED

Theorem le_phi_pairs_generated:
  !pairs. phi_pairs (mk_phi_ops_from_pairs pairs) = pairs
Proof
  Induct >> simp[mk_phi_ops_from_pairs_def, phi_pairs_def] >>
  gen_tac >> PairCases_on `h` >> simp[mk_phi_ops_from_pairs_def, phi_pairs_def]
QED

Theorem le_collected_phi_input_available:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\ le_configured_context ctx /\
  MEM pa (collect_phi_actions (fn_max_inst_id fn) ctx (cfg_analyze fn)
    (load_analyze ctx fn) fn) /\
  MEM (pred,v) (phi_pairs pa.pa_phi_ops) ==>
  ?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
    fn_cfg_edge fn pred pa.pa_join_lbl /\ def_available_at fn pb NONE v
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >>
  `MEM (pred,v) pairs` by gvs[le_phi_pairs_generated] >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl)` by
    (qpat_x_assum `MAP FST pairs = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[MEM_MAP] >> qexists `(pred,v)` >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) pred))
    (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) inst) = SOME [Var v]` by
    (fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `MEM pred (fn_labels fn)` by metis_tac[cfg_analyze_pred_labels] >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred` by
    (gvs[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  qexists `pb` >> simp[] >> conj_tac
  >- metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  irule le_static_boundary_singleton_available >> metis_tac[]
QED
