Theory loadElimReachedBatchSuccess
Ancestors
  loadElimReachedSourceAgreement loadElimPhiSuccess loadElimOriginHelpers
  loadElimDefs venomExecSemantics list finite_map

Theorem le_occ_prefix_collected_phis_success:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
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
  strip_tac >> irule le_eval_phis_prefix_success >>
  conj_tac >- metis_tac[] >>
  simp[phis_for_block_def, EVERY_MAP, EVERY_FILTER] >>
  pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> rpt strip_tac >>
  drule collect_phi_actions_member >> strip_tac >>
  qmatch_goalsub_abbrev_tac `eval_one_phi r g` >>
  qmatch_asmsub_abbrev_tac `compute_phi_action m _ _ key _ _` >>
  `g.inst_operands = e.pa_phi_ops /\ g.inst_outputs = [e.pa_phi_out]` by
    simp[Abbr `g`] >>
  `bb.bb_label = e.pa_join_lbl` by metis_tac[] >>
  `ALL_DISTINCT (cfg_preds_of (cfg_analyze fn) e.pa_join_lbl)` by metis_tac[] >>
  drule_all le_occ_prefix_phi_selected_source_eval >> strip_tac >>
  metis_tac[]
QED
