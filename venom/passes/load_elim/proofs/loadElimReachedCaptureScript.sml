Theory loadElimReachedCapture
Ancestors
  loadElimReachedAvailability loadElimPhiCapture loadElimDefs
  loadElimOccurrence venomState venomExecSemantics finite_map list

Theorem le_occ_prefix_phi_selected_eval:
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
  (!v w. lookup_var v u = SOME w ==> lookup_var v r = SOME w) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  g.inst_operands = pa.pa_phi_ops /\ g.inst_outputs = [pa.pa_phi_out] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    eval_one_phi r g = SOME (pa.pa_phi_out,w)
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_value >> strip_tac >>
  `eval_one_phi r g = SOME (pa.pa_phi_out,w)` by
    (irule le_generated_phi_eval >> metis_tac[]) >>
  metis_tac[]
QED

Theorem le_occ_prefix_phi_selected_capture:
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
  (!v w. lookup_var v u = SOME w ==> lookup_var v r = SOME w) /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl) /\
  MEM pa actions /\ ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  eval_phis r (phis_for_block actions pa.pa_join_lbl ++ rest) = OK q ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected_value >> strip_tac >>
  `lookup_var pa.pa_phi_out q = SOME w` by
    (irule le_phi_action_capture >> metis_tac[]) >>
  metis_tac[]
QED
