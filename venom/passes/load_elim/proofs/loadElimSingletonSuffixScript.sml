Theory loadElimSingletonSuffix
Ancestors
  loadElimDefinitionCuts loadElimActualGeneration loadElimOccurrenceCoverage
  loadElimTransferProvenance loadElimOccurrence loadElimDefs
  dfAnalyzeDefs cfgDefs cfgAnalysisProps venomWf venomExecProofs venomInstProps
  sccpCorrectnessProofs simplifyCfgPhiSemantics finite_map list rich_list

Definition le_singleton_retained_occ_def:
  (le_singleton_retained_occ ctx fn key op (StepOcc bb n fuel u t) <=>
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label n))
      key = SOME [op] /\
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label (SUC n)))
      key = SOME [op] /\
    ~le_transfer_generates ctx (EL n bb.bb_instructions) key op) /\
  (le_singleton_retained_occ ctx fn key op (PhiOcc bb u t) <=>
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label 0))
      key = SOME [op])
End

Theorem le_occ_prefix_singleton_suffix:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !ctx key op.
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  ?pre bb n fuel u t suffix.
    es = pre ++ StepOcc bb n fuel u t :: suffix /\
    le_transfer_generates ctx (EL n bb.bb_instructions) key op /\
    FLOOKUP (unwrap_load_lattice
      (df_at NONE (load_analyze ctx fn) bb.bb_label (SUC n))) key = SOME [op] /\
    EVERY (le_singleton_retained_occ ctx fn key op) suffix
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- suspend "start"
  >- suspend "next"
  >> suspend "block"
QED

Resume le_occ_prefix_singleton_suffix[start]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `p.vs_current_bb = s0.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `MEM s0.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[sccpProofsBaseTheory.entry_label_in_dfs_pre] >> gvs[] >>
  `unwrap_load_lattice (df_at NONE (load_analyze ctx fn) s0.vs_current_bb
     (phi_prefix_length bb.bb_instructions)) =
   unwrap_load_lattice (df_at NONE (load_analyze ctx fn) s0.vs_current_bb 0)` by
    (irule le_analyze_phi_prefix_lookup >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s0.vs_current_bb 0)) key = NONE` by
    (irule le_analyze_entry_no_lookup >> simp[] >> metis_tac[]) >> gvs[]
QED

Resume le_occ_prefix_singleton_suffix[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >> gvs[] >>
  Cases_on `le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op`
  >- (qexistsl [`es`, `bb`, `s.vs_inst_idx`, `k`, `s`, `u`, `[]`] >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op]` by
    (drule_at (Pat `FLOOKUP _ _ = SOME [_]`) le_analyze_singleton_step >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`pre`, `bb'`, `n`, `fuel`, `u'`, `t`,
    `suffix ++ [StepOcc bb s.vs_inst_idx k s u]`] >>
  simp[le_singleton_retained_occ_def, APPEND_ASSOC]
QED

Resume le_occ_prefix_singleton_suffix[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  `fn_cfg_edge fn bb.bb_label u.vs_current_bb` by
    metis_tac[le_active_terminator_edge] >>
  `bb.bb_label = s.vs_current_bb /\ p.vs_current_bb = u.vs_current_bb` by
    metis_tac[lookup_block_label, eval_phis_preserves_current_bb] >>
  `MEM u.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_cfg_edge_in_dfs_pre] >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) u.vs_current_bb)` by
    (gvs[fn_cfg_edge_def] >>
     metis_tac[cfg_edge_symmetry_uncond, bb_succs_in_cfg_succs,
       wf_function_def, lookup_block_label]) >> gvs[] >>
  `unwrap_load_lattice (df_at NONE (load_analyze ctx fn) u.vs_current_bb
     (phi_prefix_length next.bb_instructions)) =
   unwrap_load_lattice (df_at NONE (load_analyze ctx fn) u.vs_current_bb 0)` by
    (irule le_analyze_phi_prefix_lookup >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     u.vs_current_bb 0)) key = SOME [op]` by metis_tac[] >>
  `FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn)
     s.vs_current_bb)) key = SOME [op]` by
    (irule le_analyze_singleton_predecessor >> simp[] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     s.vs_current_bb (LENGTH bb.bb_instructions))) key = SOME [op]` by
    (irule le_analyze_singleton_exit >> simp[] >> metis_tac[]) >>
  `SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
    (`bb_well_formed bb` by metis_tac[wf_function_bb_well_formed, lookup_block_MEM] >>
     gvs[bb_well_formed_def] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     s.vs_current_bb (SUC s.vs_inst_idx))) key = SOME [op]` by simp[] >>
  Cases_on `le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op`
  >- (qexistsl [`es`, `bb`, `s.vs_inst_idx`, `k`, `s`, `u`, `[PhiOcc next u p]`] >>
      simp[le_singleton_retained_occ_def] >> metis_tac[lookup_block_label]) >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op]` by
    (drule_at (Pat `FLOOKUP _ _ = SOME [_]`) le_analyze_singleton_step >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`pre`, `bb'`, `n`, `fuel`, `u'`, `t`,
    `suffix ++ [StepOcc bb s.vs_inst_idx k s u; PhiOcc next u p]`] >>
  simp[le_singleton_retained_occ_def, APPEND_ASSOC] >> metis_tac[lookup_block_label]
QED
Finalise le_occ_prefix_singleton_suffix
