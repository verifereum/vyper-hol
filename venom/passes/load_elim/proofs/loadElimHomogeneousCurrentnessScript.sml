Theory loadElimHomogeneousCurrentness
Ancestors
  loadElimSingletonSuffix loadElimSingletonCurrentness loadElimSelectedGeneration loadElimNormalizedCuts
  loadElimActualGeneration loadElimSolverProvenance loadElimNonempty loadElimExitCurrentness
  loadElimTransferProvenance loadElimOccurrence loadElimDefs
  loadElimPopulation loadElimOccurrenceCoverage loadElimOperationalHistory analysisSimProofsBase
  loadElimLatestRead loadElimKeyRead loadElimKeyShapeInvariant loadElimConfiguredGeneration
  loadElimAbsoluteKey loadElimGenerationSound loadElimOccurrenceRead dfgCorrectnessProof venomExecProps words pred_set
  loadElimReachableSSA loadElimOperandValidity loadElimNormalizeHelpers
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

Theorem le_homogeneous_occ_value_no_write:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  le_homogeneous_retained_occ ctx fn key (Var v) e ==>
  v NOTIN le_occ_writes e
Proof
  strip_tac >>
  Cases_on `e`
  >- (drule_all le_occ_step_static >> strip_tac >>
      fs[le_homogeneous_retained_occ_def, le_occ_writes_def] >> strip_tac >>
      drule_all le_ordinary_definition_normalized_cut >> simp[]) >>
  drule_all le_occ_phi_static >> strip_tac >>
  fs[le_homogeneous_retained_occ_def, le_occ_writes_def] >>
  strip_tac >> fs[le_phi_outputs_def, MEM_FLAT, MEM_MAP] >>
  `MEM i' b.bb_instructions` by
    (fs[le_phi_prefix_take] >> metis_tac[MEM_TAKE]) >>
  `i'.inst_opcode = PHI` by
    (mp_tac (Q.SPEC `b.bb_instructions` phi_prefix_all_phi) >>
     fs[le_phi_prefix_take, EVERY_MEM]) >>
  metis_tac[le_phi_definition_normalized_cut]
QED

Theorem le_homogeneous_occ_read_local:
  wf_function fn /\ fn_inst_wf fn /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  (!b n fuel x y. MEM (StepOcc b n fuel x y) es ==>
    le_inst_operands_valid ctx.lctx_dfg (EL n b.bb_instructions) x) /\
  le_homogeneous_retained_occ ctx fn key r e /\
  le_absolute_key ctx.lctx_addr_space key /\
  le_key_address ctx.lctx_addr_space key (le_occ_pre e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a (le_occ_after e) =
  le_read_address ctx.lctx_addr_space a (le_occ_pre e)
Proof
  strip_tac >> Cases_on `e`
  >- (`le_occ_valid C fn (StepOcc b n n0 v v0)` by
        metis_tac[le_occ_prefix_member] >>
      `MEM b.bb_label (cfg_analyze fn).cfg_dfs_pre` by
        metis_tac[le_occ_step_dfs] >>
      `inst_wf (EL n b.bb_instructions)` by metis_tac[le_occ_step_wf] >>
      `df_at NONE (load_analyze ctx fn) b.bb_label (SUC n) =
        load_transfer ctx (EL n b.bb_instructions)
          (df_at NONE (load_analyze ctx fn) b.bb_label n)` by
        (irule le_analyze_step_transfer >> fs[le_occ_valid_def] >>
         metis_tac[lookup_block_label]) >>
      fs[le_read_address_occ_after, le_occ_pre_def, le_occ_post_def,
         le_occ_valid_def, le_homogeneous_retained_occ_def] >>
      irule le_configured_retained_step_read_local >> metis_tac[]) >>
  `le_occ_valid C fn (PhiOcc b v v0)` by metis_tac[le_occ_prefix_member] >>
  metis_tac[le_phi_read_occ_after]
QED


Theorem le_occ_prefix_homogeneous_current_local:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u) /\
  (!bb n fuel u t op. MEM (StepOcc bb n fuel u t) es /\
    le_transfer_generates ctx (EL n bb.bb_instructions) key op ==>
    le_chain_valid ctx.lctx_dfg [] op t) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\ EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) vs ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand r s
Proof
  strip_tac >> drule_all le_occ_prefix_homogeneous_suffix >> strip_tac >>
  qpat_x_assum `es = _` SUBST_ALL_TAC >>
  `MEM (StepOcc bb n fuel u t) (pre ++ StepOcc bb n fuel u t::suffix)` by simp[] >>
  `le_occ_valid C fn (StepOcc bb n fuel u t)` by metis_tac[le_occ_prefix_member] >>
  `MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
   n < LENGTH bb.bb_instructions /\
   (EL n bb.bb_instructions).inst_opcode <> PHI` by
    (irule le_occ_step_static >> simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  `(!v. key = LK_Op (Var v) ==> ~MEM v (EL n bb.bb_instructions).inst_outputs)` by
    (rpt strip_tac >> gvs[] >> drule_all le_generator_key_output_separate >> simp[]) >>
  `le_absolute_key ctx.lctx_addr_space key` by metis_tac[le_generated_key_absolute] >>
  `step_inst fuel C (EL n bb.bb_instructions) u = OK t` by fs[le_occ_valid_def] >>
  `le_inst_operands_valid ctx.lctx_dfg (EL n bb.bb_instructions) u` by metis_tac[] >>
  `le_chain_valid ctx.lctx_dfg [] op t` by metis_tac[] >>
  `le_key_read ctx.lctx_addr_space key t = eval_operand op t` by
    (irule le_configured_generation_read_local >> simp[] >> metis_tac[]) >>
  `eval_operand op t = eval_operand r t` by metis_tac[le_chain_valid_eval] >>
  drule_all le_configured_generation_address_local >> strip_tac >>
  `!v. key = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    suspend "key" >>
  `le_key_address ctx.lctx_addr_space key s = le_key_address ctx.lctx_addr_space key t` by
    (drule_all le_prefix_suffix_key_address >> simp[le_occ_post_def]) >>
  `le_read_address ctx.lctx_addr_space a s = le_read_address ctx.lctx_addr_space a t` by
    suspend "read" >>
  `eval_operand r s = eval_operand r t` by suspend "operand" >>
  gvs[le_key_read_def]
QED

Resume le_occ_prefix_homogeneous_current_local[key]:
  rpt gen_tac >> disch_tac >> simp[EVERY_MEM] >> gen_tac >> disch_tac >>
  irule le_present_occ_key_no_write >>
  qexistsl [`C`, `ctx`, `pre ++ StepOcc bb n fuel u t::suffix`, `fn`, `i`, `s`, `s0`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[EVERY_MEM, le_homogeneous_step_presence]) >>
  rpt strip_tac >> gvs[] >> metis_tac[EVERY_MEM, le_homogeneous_phi_presence]
QED

Resume le_occ_prefix_homogeneous_current_local[read]:
  `le_occ_chain (le_occ_after (StepOcc bb n fuel u t)) suffix s` by
    (drule le_occ_prefix_chain >> simp[le_occ_chain_append, le_occ_chain_def] >> metis_tac[]) >>
  `EVERY (le_occ_valid C fn) suffix` by
    (drule le_occ_prefix_valid >> simp[]) >>
  `EVERY (\q. !a. le_key_address ctx.lctx_addr_space key (le_occ_pre q) = SOME a /\
    a < dimword (:256) ==>
    le_read_address ctx.lctx_addr_space a (le_occ_after q) =
    le_read_address ctx.lctx_addr_space a (le_occ_pre q)) suffix` by
    (simp[EVERY_MEM] >> rpt strip_tac >> irule le_homogeneous_occ_read_local >>
     simp[] >> qexistsl [`C`, `pre ++ StepOcc bb n fuel u t::suffix`, `fn`, `i`, `key`, `r`, `s`, `s0`] >>
     simp[] >> reverse conj_tac
     >- (qpat_x_assum `EVERY (le_homogeneous_retained_occ _ _ _ _) _` mp_tac >>
         simp[EVERY_MEM]) >>
     gvs[MEM_APPEND, MEM] >> metis_tac[]) >>
  `le_key_address ctx.lctx_addr_space key (le_occ_after (StepOcc bb n fuel u t)) = SOME a` by
    simp[le_absolute_key_after_post, le_occ_post_def] >>
  drule_all le_occ_chain_retained_read >> simp[le_read_address_occ_after, le_occ_post_def]
QED

Resume le_occ_prefix_homogeneous_current_local[operand]:
  irule le_key_address_operand_injective >> qexists `ctx.lctx_addr_space` >>
  `!v. LK_Op r = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    (rpt gen_tac >> disch_tac >> gvs[] >> simp[EVERY_MEM] >>
     gen_tac >> disch_tac >> irule le_homogeneous_occ_value_no_write >>
     qexistsl [`C`, `ctx`, `pre ++ StepOcc bb n fuel u t::suffix`, `fn`, `i`, `key`, `s`, `s0`] >>
     simp[] >> metis_tac[EVERY_MEM]) >>
  `le_absolute_key ctx.lctx_addr_space (LK_Op r)` by simp[le_absolute_key_def] >>
  drule_all le_prefix_suffix_key_address >> simp[le_occ_post_def]
QED
Finalise le_occ_prefix_homogeneous_current_local

Theorem le_homogeneous_occ_read:
  wf_function fn /\ fn_inst_wf fn /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  (!b n fuel x y. MEM (StepOcc b n fuel x y) es ==> dfg_assigns_sound ctx.lctx_dfg x) /\
  le_homogeneous_retained_occ ctx fn key r e /\
  le_absolute_key ctx.lctx_addr_space key /\
  le_key_address ctx.lctx_addr_space key (le_occ_pre e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a (le_occ_after e) =
  le_read_address ctx.lctx_addr_space a (le_occ_pre e)
Proof
  strip_tac >> irule le_homogeneous_occ_read_local >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `key`, `r`, `s`, `s0`] >> simp[] >>
  metis_tac[le_dfg_sound_inst_operands_valid]
QED

Theorem le_occ_prefix_homogeneous_current:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    dfg_assigns_sound ctx.lctx_dfg u /\ dfg_assigns_sound ctx.lctx_dfg t) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\ EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) vs ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand r s
Proof
  strip_tac >> irule le_occ_prefix_homogeneous_current_local >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `s0`, `vs`] >> simp[] >>
  metis_tac[le_dfg_sound_inst_operands_valid, le_dfg_sound_chain_valid]
QED

Theorem le_occ_prefix_store_test_current:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
    dfg_assigns_sound ctx.lctx_dfg u /\ dfg_assigns_sound ctx.lctx_dfg t) /\
  dfg_assigns_sound ctx.lctx_dfg s /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\
  EVERY (\a. case (a,value) of (Var _,Var _) =>
    normalize_operand ctx.lctx_dfg [] a = normalize_operand ctx.lctx_dfg [] value
    | _ => a = value) vs ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand value s
Proof
  strip_tac >>
  `EVERY (\op. normalize_operand ctx.lctx_dfg [] op =
     normalize_operand ctx.lctx_dfg [] value) vs` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `op` >> Cases_on `value` >> simp[]) >>
  `le_key_read ctx.lctx_addr_space key s =
     eval_operand (normalize_operand ctx.lctx_dfg [] value) s` by
    (irule le_occ_prefix_homogeneous_current >> simp[] >>
     qexistsl [`C`, `es`, `fn`, `i`, `s0`, `vs`] >> gvs[] >>
     first_assum ACCEPT_TAC) >>
  metis_tac[normalize_operand_eval_proof]
QED

(* Reachable-discharge audit for the explicit DFG premises above.
   These theorems are semantic boundaries, not yet a wrapper discharging
   those premises from the frozen theorem.

   For each StepOcc bb n fuel u t, le_occ_prefix_member and
   le_occ_valid_def supply the successful step; le_occ_step_wf supplies
   inst_wf, and lookup_block_MEM supplies block membership.  The frozen
   universal step premise supplies soundness at t with index reset IF
   all five invariants hold at u with index reset.  dfg_assigns_sound
   depends only on vs_vars (and hence ignores index reset).  This gives
   precisely the extra generator-post-state soundness used at line 282,
   not merely soundness of the generator input.

   Propagating the five invariants to every reached input is still an
   integration obligation.  The start and block clauses of le_occ_prefix
   require whole-batch PHI preservation before the next step.  The frozen
   PHI premise supplies its DFG component at reachable blocks; the empty
   BP result makes bp_ptr_sound and bp_ptrs_bounded vacuous; and
   venomExecProofs.eval_phis_preserves_alloca_fields supplies the unchanged
   allocation fields for allocas_non_overlapping and allocas_in_word.
   Index changes between occurrences affect none of these predicates.
   Initial nonoverlap comes from alloca_inv.  DFS reachability is needed
   to apply the frozen PHI premise (le_occ_phi_static gives it).

   No reached-invariant induction is claimed here.  In particular the
   step premise cannot be applied using DFG soundness alone.  A separate
   checked occurrence-invariant wrapper must discharge that induction
   before the exact store-test theorem is used under the frozen premises.
*)
