Theory loadElimReachedSourceAgreement
Ancestors
  loadElimReachedCapture loadElimReachedAvailability loadElimSingletonSuffix
  loadElimTransferProvenance cfgNormBase cfgNormProof cfgTransform
  loadElimActionFreshness loadElimOccurrence loadElimActualGeneration
  loadElimExitCurrentness loadElimPhiCapture makeSsaHelper list finite_map pred_set

Theorem le_generating_var_source:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  le_transfer_generates ctx inst key (Var v) ==>
  MEM v (fn_all_vars fn)
Proof
  strip_tac >> fs[le_transfer_generates_def] >>
  metis_tac[inst_output_in_fn_all_vars, inst_operand_var_in_fn_all_vars, MEM]
QED

Theorem le_occ_prefix_singleton_source_var:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [Var v] ==>
  MEM v (fn_all_vars fn)
Proof
  strip_tac >> drule_all le_occ_prefix_singleton_suffix >> strip_tac >>
  `MEM (StepOcc bb n fuel u t) es` by simp[MEM_APPEND] >>
  drule_all le_occ_step_static >> strip_tac >>
  irule le_generating_var_source >> metis_tac[EL_MEM]
QED

Theorem le_occ_prefix_exit_singleton_source_var:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  is_terminator i.inst_opcode /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) s.vs_current_bb)) key = SOME [Var v] ==>
  MEM v (fn_all_vars fn)
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_terminator_end >> strip_tac >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb (LENGTH bb.bb_instructions))) key = SOME [Var v]` by
    (irule le_analyze_singleton_exit >> simp[] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb s.vs_inst_idx)) key = SOME [Var v]` by
    (`FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
        s.vs_current_bb s.vs_inst_idx)) key = SOME [Var v] \/
      le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key (Var v)` by
       (irule le_analyze_singleton_step >> simp[] >> metis_tac[]) >>
     metis_tac[le_configured_terminator_no_generation]) >>
  irule le_occ_prefix_singleton_source_var >> metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_value:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') ==>
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
  strip_tac >> drule_all le_occ_prefix_phi_selected_value >> strip_tac >>
  `prev.bb_label = t.vs_current_bb` by metis_tac[lookup_block_label] >>
  `MEM v (fn_all_vars fn)` by
    (irule le_occ_prefix_exit_singleton_source_var >> metis_tac[]) >>
  metis_tac[]
QED

(* A selected incoming variable belongs to the current source domain.
   No global convention for generated names is needed at this boundary. *)
Theorem le_occ_prefix_phi_selected_source_eval_domain:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
  r.vs_prev_bb = u.vs_prev_bb /\
  (!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_source_value >> strip_tac >>
  `lookup_var v r = SOME w` by metis_tac[] >>
  `eval_one_phi r g = SOME (pa.pa_phi_out,w)` by
    (irule le_generated_phi_eval >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_eval_disjoint:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
  r.vs_prev_bb = u.vs_prev_bb /\
  DISJOINT G (set (fn_all_vars fn)) /\
  (!v. v NOTIN G ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >> irule le_occ_prefix_phi_selected_source_eval_domain >>
  simp[] >> fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_eval:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
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
  drule_all le_occ_prefix_phi_selected_source_eval_domain >> simp[]
QED

Theorem le_occ_prefix_phi_selected_source_capture_domain:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
  r.vs_prev_bb = u.vs_prev_bb /\
  (!v. MEM v (fn_all_vars fn) ==> lookup_var v u = lookup_var v r) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  MEM pa actions /\ ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  eval_phis r (phis_for_block actions pa.pa_join_lbl ++ rest) = OK q ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_source_value >> strip_tac >>
  `lookup_var v r = SOME w` by metis_tac[] >>
  `lookup_var pa.pa_phi_out q = SOME w` by
    (irule le_phi_action_capture >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_source_capture_disjoint:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
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
  drule_all le_occ_prefix_phi_selected_source_capture_domain >> simp[]
QED

Theorem le_occ_prefix_phi_selected_source_capture:
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
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
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
  drule_all le_occ_prefix_phi_selected_source_capture_domain >> simp[]
QED
