Theory loadElimCaptureEntry
Ancestors
  loadElimCaptureInvariant loadElimDefs loadElimOccurrence loadElimKeyRead
  loadElimActualPhiFrame loadElimReachedSourceAgreement loadElimInitialEntryActions
  loadElimTargetWrites loadElimOccurrenceInversion loadElimActionFreshness
  loadElimOperationalHistory loadElimHistoryHelpers venomExecSemantics
  list rich_list finite_map

Theorem le_latest_captures_phi:
  le_latest_captures m ctx cfg result actions h r /\
  (!pa. MEM pa actions /\ bb.bb_label <> pa.pa_join_lbl ==>
    lookup_var pa.pa_phi_out q = lookup_var pa.pa_phi_out r) /\
  (!pa key lbl inst. MEM pa actions /\ bb.bb_label = pa.pa_join_lbl /\
    compute_phi_action m cfg result key lbl inst = SOME pa ==>
    ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
      lookup_var pa.pa_phi_out q = SOME w) ==>
  le_latest_captures m ctx cfg result actions (h ++ [PhiOcc bb u p]) q
Proof
  simp[le_latest_captures_def] >> rpt strip_tac >>
  qpat_x_assum `_ ++ [_] = _` mp_tac >>
  once_rewrite_tac[APPEND_EQ_APPEND] >> strip_tac >>
  gvs[APPEND_EQ_CONS] >>
  first_x_assum irule >> simp[]
  >- (conj_tac
      >- (qexistsl [`bb'`, `p'`, `pre`] >> simp[] >> metis_tac[])
      >> metis_tac[])
  >- (conj_tac
      >- (qexistsl [`bb'`, `p'`, `pre`] >> simp[])
      >> metis_tac[])
  >> metis_tac[]
QED

Theorem le_occ_prefix_actual_phis_captures:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (h ++ [PhiOcc bb u p]) i s /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
    (h ++ [PhiOcc bb u p]) ==> dfg_assigns_sound ctx.lctx_dfg u') /\
  r.vs_prev_bb = u.vs_prev_bb /\ r.vs_labels = u.vs_labels /\
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  padded_exec_equiv {v | isPREFIX "$le_phi_" v} u r /\
  ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
  le_latest_captures m ctx (cfg_analyze fn) (load_analyze ctx fn)
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) h r ==>
  ?q. eval_phis r
    (analysis_block_transform_prepend NONE (load_analyze ctx fn)
      (load_phi_prepend (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))
      (\ll inst. [load_elim_inst ctx
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ll inst]) bb).bb_instructions = OK q /\
    padded_exec_equiv {v | isPREFIX "$le_phi_" v} p q /\
    q.vs_current_bb = r.vs_current_bb /\ q.vs_inst_idx = r.vs_inst_idx /\
    q.vs_prev_bb = r.vs_prev_bb /\ q.vs_labels = r.vs_labels /\
    le_latest_captures m ctx (cfg_analyze fn) (load_analyze ctx fn)
      (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
      (h ++ [PhiOcc bb u p]) q
Proof
  strip_tac >>
  `le_occ_prefix C fn s0 (h ++ PhiOcc bb u p :: []) i s` by simp[] >>
  drule_all le_occ_prefix_actual_phis_frame >>
  disch_then (qspec_then `m` (qx_choose_then `q` strip_assume_tac)) >>
  `!v. ~isPREFIX "$le_phi_" v ==> lookup_var v u = lookup_var v r` by
    fs[loadElimMemoryRelTheory.padded_exec_equiv_def] >>
  `eval_phis r [] = OK r` by simp[eval_phis_def] >>
  drule_all loadElimDynamicCaptureTheory.le_occ_prefix_all_entries_phis_success >>
  disch_then (qspec_then `m` (qx_choose_then `z` assume_tac)) >>
  `eval_phis r (phis_for_block
    (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
    bb.bb_label) = OK z` by fs[] >>
  drule le_occ_prefix_phi_semantics >> strip_tac >>
  `MEM bb fn.fn_blocks` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `!pa. MEM pa (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn) ==>
    lookup_var pa.pa_phi_out q = lookup_var pa.pa_phi_out z` by
    (rpt strip_tac >> irule le_actual_prepend_generated_lookup >> simp[] >>
     qexistsl [`collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn`,
       `bb`, `ctx`, `r`, `load_analyze ctx fn`] >>
     simp[] >>
     drule_all le_collected_action_source_disjoint >> strip_tac >>
     rpt strip_tac >>
     qpat_x_assum `~MEM _ (fn_all_vars fn)` mp_tac >>
     simp[cfgTransformTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[]) >>
  qexists_tac `q` >> simp[] >>
  irule le_latest_captures_phi >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `h = []`
      >- (drule le_occ_prefix_phi_inversion >> simp[] >> strip_tac >>
          `bb.bb_label = s0.vs_current_bb` by
            metis_tac[venomExecPropsTheory.lookup_block_label] >>
          metis_tac[le_collected_action_nonentry]) >>
      `ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl)` by metis_tac[] >>
      `eval_phis r (phis_for_block
         (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
         pa.pa_join_lbl ++ []) = OK z` by metis_tac[APPEND_NIL] >>
      `ALL_DISTINCT (MAP (\a. a.pa_phi_out)
        (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn))` by
        simp[le_collected_action_outputs_distinct] >>
      drule_all le_occ_prefix_phi_selected_source_capture >>
      strip_tac >> metis_tac[]) >>
  qexists_tac `r` >> simp[] >> rpt strip_tac >>
  `pa.pa_phi_out NOTIN le_phi_outputs (phis_for_block
     (collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn)
     bb.bb_label ++ [])` by
    (irule le_selected_output_other_join >>
     simp[le_collected_action_outputs_distinct, le_phi_outputs_def, le_phi_prefix_def] >>
     metis_tac[]) >>
  qpat_x_assum `eval_phis r (phis_for_block _ _ ++ []) = OK z`
    (mp_tac o MATCH_MP le_eval_phis_event) >>
  simp[le_framed_history_def] >> strip_tac >> fs[]
QED
