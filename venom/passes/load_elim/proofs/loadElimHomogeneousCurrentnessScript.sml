Theory loadElimHomogeneousCurrentness
Ancestors
  loadElimSingletonSuffix loadElimSingletonCurrentness loadElimSelectedGeneration loadElimNormalizedCuts
  loadElimActualGeneration loadElimSolverProvenance loadElimNonempty loadElimExitCurrentness
  loadElimTransferProvenance loadElimOccurrence loadElimDefs
  loadElimPopulation loadElimOccurrenceCoverage
  dfAnalyzeDefs cfgDefs cfgAnalysisProps venomWf venomExecProofs venomInstProps
  sccpCorrectnessProofs simplifyCfgPhiSemantics simplifyCfgPhiRepair
  simplifyCfgStruct finite_map list rich_list

Definition le_homogeneous_retained_occ_def:
  (le_homogeneous_retained_occ ctx fn key r (StepOcc bb n fuel u t) <=>
    ?vs. vs <> [] /\ EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) vs /\
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME vs /\
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label (SUC n))) key = SOME vs /\
    (!op. ~le_transfer_generates ctx (EL n bb.bb_instructions) key op)) /\
  (le_homogeneous_retained_occ ctx fn key r (PhiOcc bb u t) <=>
    ?vs. vs <> [] /\ EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) vs /\
    FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) bb.bb_label 0)) key = SOME vs)
End

Theorem le_analyze_list_step[local]:
  wf_function fn /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ n < LENGTH bb.bb_instructions /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl (SUC n))) key = SOME vs ==>
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) lbl n)) key = SOME vs \/
  ?op. vs = [op] /\ le_transfer_generates ctx (EL n bb.bb_instructions) key op
Proof
  strip_tac >> drule_all le_analyze_step_transfer >> strip_tac >>
  gvs[] >> drule le_transfer_lookup_origin >> simp[]
QED

Theorem le_occ_prefix_homogeneous_suffix:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !ctx key vs r.
  wf_function fn /\ fn_inst_wf fn /\ le_configured_context ctx /\
  ctx.lctx_dfg = dfg_build_function fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\ EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) vs ==>
  ?pre bb n fuel u t suffix op.
    es = pre ++ StepOcc bb n fuel u t :: suffix /\
    le_transfer_generates ctx (EL n bb.bb_instructions) key op /\
    normalize_operand ctx.lctx_dfg [] op = r /\
    FLOOKUP (unwrap_load_lattice
      (df_at NONE (load_analyze ctx fn) bb.bb_label (SUC n))) key = SOME [op] /\
    EVERY (le_homogeneous_retained_occ ctx fn key r) suffix
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- suspend "start"
  >- suspend "next"
  >> suspend "block"
QED

Resume le_occ_prefix_homogeneous_suffix[start]:
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

Resume le_occ_prefix_homogeneous_suffix[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >> gvs[] >>
  Cases_on `?op. le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op`
  >- (pop_assum (qx_choose_then `op` assume_tac) >>
      `df_at NONE (load_analyze ctx fn) s.vs_current_bb (SUC s.vs_inst_idx) =
       load_transfer ctx (EL s.vs_inst_idx bb.bb_instructions)
         (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)` by
        (irule le_analyze_step_transfer >> simp[]) >>
      `vs = [op]` by metis_tac[le_transfer_generates_lookup, optionTheory.SOME_11] >>
      gvs[] >> qexistsl [`es`, `bb`, `s.vs_inst_idx`, `k`, `s`, `u`, `[]`, `op`] >> simp[]) >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs` by
    (drule_at (Pat `FLOOKUP _ _ = SOME _`) le_analyze_list_step >> simp[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`ctx`, `key`, `vs`, `r`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl [`pre`, `bb'`, `n`, `fuel`, `u'`, `t`,
    `suffix ++ [StepOcc bb s.vs_inst_idx k s u]`, `op`] >>
  simp[le_homogeneous_retained_occ_def, APPEND_ASSOC] >> metis_tac[]
QED

Resume le_occ_prefix_homogeneous_suffix[block]:
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
     u.vs_current_bb 0)) key = SOME vs` by metis_tac[] >>
  `?m. df_boundary NONE (load_analyze ctx fn) s.vs_current_bb = SOME m` by
    metis_tac[le_analyze_boundary_some] >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`) le_analyze_selected_predecessor >>
  simp[] >> disch_then (qspecl_then [`s.vs_current_bb`, `m`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `ws` strip_assume_tac) >>
  `FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn)
     s.vs_current_bb)) key = SOME ws` by simp[unwrap_load_lattice_def] >>
  `?exit. df_at NONE (load_analyze ctx fn) s.vs_current_bb
     (LENGTH bb.bb_instructions) = SOME exit` by
    (irule le_analyze_at_some >> simp[]) >>
  drule_at (Pat `FLOOKUP (unwrap_load_lattice (df_boundary _ _ _)) _ = SOME _`)
    le_analyze_selected_exit >> simp[] >>
  disch_then (qx_choose_then `zs` strip_assume_tac) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     s.vs_current_bb (LENGTH bb.bb_instructions))) key = SOME zs` by
    simp[unwrap_load_lattice_def] >>
  `zs <> []` by metis_tac[le_analyze_point_lookup_nonempty] >>
  `EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) zs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `SUC s.vs_inst_idx = LENGTH bb.bb_instructions` by
    (`bb_well_formed bb` by metis_tac[wf_function_bb_well_formed, lookup_block_MEM] >>
     gvs[bb_well_formed_def] >> metis_tac[]) >>
  `!op. ~le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op` by
    metis_tac[le_configured_terminator_no_generation] >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb (SUC s.vs_inst_idx))) key = SOME zs` by simp[unwrap_load_lattice_def] >>
  `FLOOKUP (unwrap_load_lattice
     (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME zs` by
    (drule_at (Pat `FLOOKUP _ _ = SOME _`) le_analyze_list_step >> simp[] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`ctx`, `key`, `zs`, `r`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl [`pre`, `bb'`, `n`, `fuel`, `u'`, `t`,
    `suffix ++ [StepOcc bb s.vs_inst_idx k s u; PhiOcc next u p]`, `op`] >>
  simp[le_homogeneous_retained_occ_def, APPEND_ASSOC] >>
  conj_tac >- gvs[unwrap_load_lattice_def] >>
  metis_tac[lookup_block_label]
QED
Finalise le_occ_prefix_homogeneous_suffix

Theorem le_homogeneous_step_presence:
  le_homogeneous_retained_occ ctx fn key r (StepOcc bb n fuel u t) ==>
  ?vs. FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label n)) key = SOME vs /\
    FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label (SUC n))) key = SOME vs /\
    (!op. vs = [op] ==> ~le_transfer_generates ctx (EL n bb.bb_instructions) key op)
Proof
  simp[le_homogeneous_retained_occ_def] >> metis_tac[]
QED

Theorem le_homogeneous_phi_presence:
  le_homogeneous_retained_occ ctx fn key r (PhiOcc bb u t) ==>
  ?vs. FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) bb.bb_label 0)) key = SOME vs
Proof
  simp[le_homogeneous_retained_occ_def] >> metis_tac[]
QED
