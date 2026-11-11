Theory loadElimStaticPhiPlacement
Ancestors
  loadElimPointReachability loadElimJoinPlacement loadElimOriginHelpers
  loadElimPhiCapture loadElimDefs codegenReadyCompute cfgAnalysisProps cfgDefs
  simplifyCfgDataflow venomWf venomInst venomExecProofs dfAnalyzeDefs
  list finite_map pred_set

Theorem le_static_multivalue_join_dominates:
  wf_function fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  n <= LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl n)) k = SOME vs /\
  1 < LENGTH vs ==>
  fn_dominates fn (find_join_block (cfg_analyze fn) {} lbl) lbl /\
  fn_entry_label fn <> SOME (find_join_block (cfg_analyze fn) {} lbl)
Proof
  strip_tac >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_analyze_point_multivalue_reachable] >>
  `fn_reachable fn lbl` by
    (drule cfg_analyze_reachable_sets >> simp[EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `MEM lbl (fn_labels fn)` by
    (fs[lookup_block_def] >> drule venomExecPropsTheory.FIND_P >> simp[] >>
     strip_tac >> drule venomExecPropsTheory.FIND_MEM >>
     simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `!path. is_fn_path fn path /\ path <> [] /\
    fn_entry_label fn = SOME (HD path) /\ LAST path = lbl ==>
    MEM (find_join_block (cfg_analyze fn) {} lbl) path /\
    fn_entry_label fn <> SOME (find_join_block (cfg_analyze fn) {} lbl)` by
    (rpt strip_tac >>
     `le_pred_path (cfg_analyze fn) path` by metis_tac[le_fn_path_pred_path] >>
     `EVERY (\l. ?b. MEM b fn.fn_blocks /\ b.bb_label = l) path` by
       (`MEM (LAST path) (fn_labels fn)` by simp[] >>
        drule_all is_fn_path_member_labels >>
        simp[EVERY_MEM, fn_labels_def, MEM_MAP] >> metis_tac[]) >>
     metis_tac[le_multivalue_point_find_join]) >>
  conj_tac
  >- (simp[fn_dominates_def] >> metis_tac[]) >>
  qpat_x_assum `fn_reachable fn lbl` mp_tac >>
  simp[fn_reachable_def] >> strip_tac >>
  drule rtc_to_fn_path >> strip_tac >> metis_tac[]
QED

Theorem le_collected_phi_join_dominates_origin:
  wf_function fn /\
  MEM pa (collect_phi_actions max_id ctx (cfg_analyze fn)
    (load_analyze ctx fn) fn) ==>
  ?bb idx inst key vs.
    MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    key = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) inst /\
    FLOOKUP (unwrap_load_lattice
      (df_at NONE (load_analyze ctx fn) bb.bb_label idx)) key = SOME vs /\
    1 < LENGTH vs /\
    compute_phi_action max_id (cfg_analyze fn) (load_analyze ctx fn)
      key bb.bb_label inst = SOME pa /\
    fn_dominates fn pa.pa_join_lbl bb.bb_label /\
    fn_entry_label fn <> SOME pa.pa_join_lbl
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule le_compute_phi_action_certificate >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> gvs[wf_function_def, fn_labels_def]) >>
  `fn_dominates fn pa.pa_join_lbl bb.bb_label /\
   fn_entry_label fn <> SOME pa.pa_join_lbl` by
    (`idx <= LENGTH bb.bb_instructions` by simp[] >>
     `1 < LENGTH vs` by fs[arithmeticTheory.GREATER_DEF] >>
     drule_all le_static_multivalue_join_dominates >> simp[]) >>
  qexistsl [`bb`, `idx`, `inst`,
    `load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) inst`, `vs`] >> simp[]
QED
