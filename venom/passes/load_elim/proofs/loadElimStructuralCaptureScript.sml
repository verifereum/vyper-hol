Theory loadElimStructuralCapture
Ancestors
  loadElimStructuralAvailability loadElimReachedSourceAgreement
  loadElimPhiCapture loadElimOccurrence loadElimDefs venomExecProofs
  venomState venomExecSemantics finite_map list pred_set

Theorem le_occ_prefix_phi_selected_source_value_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) ==>
  ?front prev j t k pairs v w.
    pre = front ++ [StepOcc prev t.vs_inst_idx k t u] /\
    le_occ_prefix C fn s0 front j t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME prev /\
    is_terminator j.inst_opcode /\ step_inst k C j t = OK u /\
    ~u.vs_halted /\ u.vs_prev_bb = SOME prev.bb_label /\
    MEM prev.bb_label (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
    pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
    MAP FST pairs = cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl /\
    MEM (prev.bb_label,v) pairs /\
    FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) prev.bb_label))
      key = SOME [Var v] /\
    lookup_var v u = SOME w /\ le_key_read ctx.lctx_addr_space key u = SOME w /\
    MEM v (fn_all_vars fn)
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_value_structural >> strip_tac >>
  `prev.bb_label = t.vs_current_bb` by metis_tac[lookup_block_label] >>
  `MEM v (fn_all_vars fn)` by
    (irule le_occ_prefix_exit_singleton_source_var >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_eval_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  (!v w. lookup_var v u = SOME w ==> lookup_var v r = SOME w) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_value_structural >> strip_tac >>
  `eval_one_phi r g = SOME (pa.pa_phi_out,w)` by
    (irule le_generated_phi_eval >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_capture_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  (!v w. lookup_var v u = SOME w ==> lookup_var v r = SOME w) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  MEM pa actions /\ ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  eval_phis r (phis_for_block actions pa.pa_join_lbl ++ rest) = OK q ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_value_structural >> strip_tac >>
  `lookup_var pa.pa_phi_out q = SOME w` by
    (irule le_phi_action_capture >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_eval_domain_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  (!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_source_value_structural >> strip_tac >>
  `lookup_var v r = SOME w` by metis_tac[] >>
  `eval_one_phi r g = SOME (pa.pa_phi_out,w)` by
    (irule le_generated_phi_eval >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_eval_disjoint_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  DISJOINT G (set (fn_all_vars fn)) /\
  (!v. v NOTIN G ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >> irule le_occ_prefix_phi_selected_source_eval_domain_structural >>
  simp[] >> fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_eval_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  (!v. ~isPREFIX "$le_phi_" v ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >>
  `!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> metis_tac[]) >>
  drule_all le_occ_prefix_phi_selected_source_eval_domain_structural >> simp[]
QED

Theorem le_occ_prefix_phi_selected_source_capture_domain_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  (!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  MEM pa actions /\ ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  eval_phis r (phis_for_block actions pa.pa_join_lbl ++ rest) = OK q ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_source_value_structural >> strip_tac >>
  `lookup_var v r = SOME w` by metis_tac[] >>
  `lookup_var pa.pa_phi_out q = SOME w` by
    (irule le_phi_action_capture >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_capture_disjoint_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  DISJOINT G (set (fn_all_vars fn)) /\
  (!v. v NOTIN G ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  MEM pa actions /\ ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  eval_phis r (phis_for_block actions pa.pa_join_lbl ++ rest) = OK q ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >>
  `!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r` by
    (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  drule_all le_occ_prefix_phi_selected_source_capture_domain_structural >> simp[]
QED

Theorem le_occ_prefix_phi_selected_source_capture_structural:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  r.vs_prev_bb = u.vs_prev_bb /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  (!v. ~isPREFIX "$le_phi_" v ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  MEM pa actions /\ ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  eval_phis r (phis_for_block actions pa.pa_join_lbl ++ rest) = OK q ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >>
  `!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> metis_tac[]) >>
  drule_all le_occ_prefix_phi_selected_source_capture_domain_structural >> simp[]
QED
