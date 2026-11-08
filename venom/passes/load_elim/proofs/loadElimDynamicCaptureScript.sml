Theory loadElimDynamicCapture
Ancestors
  loadElimReachedBatchSuccess loadElimInitialEntryActions
  loadElimOccurrenceInversion loadElimActionFreshness loadElimHistoryHelpers
  loadElimReachedSourceAgreement loadElimOriginHelpers list finite_map

(* The successful source batch remains explicit, just as in the noninitial
   interface. No agreement on generated variables is required. *)
Theorem le_occ_prefix_all_entries_phis_success:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
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
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
  eval_phis r rest = OK z ==>
  ?q. eval_phis r
    (phis_for_block (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
       bb.bb_label ++ rest) = OK q
Proof
  strip_tac >> Cases_on `pre = []`
  >- (`u = s0` by
        (drule le_occ_prefix_phi_inversion >> gvs[]) >>
      `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
        metis_tac[le_occ_prefix_phi_semantics] >>
      `fn_entry_label fn = SOME bb.bb_label` by
        metis_tac[venomExecPropsTheory.lookup_block_label] >>
      drule_all le_entry_phis_empty >> simp[] >> metis_tac[]) >>
  irule le_occ_prefix_collected_phis_success >> metis_tac[]
QED

Theorem le_occ_prefix_collected_action_capture:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
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
  eval_phis r
    (phis_for_block (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
       pa.pa_join_lbl ++ rest) = OK q ==>
  ?key lbl inst w.
    compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
    le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >>
  `pre <> []` by
    (strip_tac >>
     `u = s0` by (drule le_occ_prefix_phi_inversion >> gvs[]) >>
     `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by
       metis_tac[le_occ_prefix_phi_semantics] >>
     metis_tac[le_collected_action_nonentry, venomExecPropsTheory.lookup_block_label]) >>
  `ALL_DISTINCT (MAP (\a. a.pa_phi_out)
     (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))` by
    metis_tac[le_collected_action_outputs_distinct] >>
  drule collect_phi_actions_member >> strip_tac >>
  drule_all le_occ_prefix_phi_selected_source_capture >> strip_tac >>
  metis_tac[]
QED

(* This conditional transport is not a claim that the actual transformed
   suffix has zero epoch, nor that the original key remains unchanged. *)
Theorem le_occ_prefix_collected_action_history:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
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
  eval_phis r
    (phis_for_block (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
       pa.pa_join_lbl ++ rest) = OK q /\
  le_framed_history q h /\ le_epoch h pa.pa_phi_out = 0 ==>
  ?key lbl inst w.
    compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
    le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out (le_history_end q h) = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_collected_action_capture >> strip_tac >>
  drule_all le_history_lookup_persistence >> metis_tac[]
QED

Theorem le_occ_prefix_collected_action_success_capture:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
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
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
  eval_phis r rest = OK z ==>
  ?q key lbl inst w.
    eval_phis r
      (phis_for_block (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
         pa.pa_join_lbl ++ rest) = OK q /\
    compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
    le_key_read ctx.lctx_addr_space key u = SOME w /\
    lookup_var pa.pa_phi_out q = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_all_entries_phis_success >>
  disch_then (qspec_then `m` strip_assume_tac) >>
  `ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl)` by metis_tac[] >>
  `eval_phis r
    (phis_for_block (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
       pa.pa_join_lbl ++ rest) = OK q` by metis_tac[] >>
  drule_all le_occ_prefix_collected_action_capture >> strip_tac >> metis_tac[]
QED
