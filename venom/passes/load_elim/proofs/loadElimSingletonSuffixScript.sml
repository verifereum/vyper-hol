Theory loadElimSingletonSuffix
Ancestors
  loadElimReachableSSA loadElimDefinitionCuts loadElimActualGeneration loadElimOccurrenceCoverage
  loadElimSingletonAvailability loadElimOperationalHistory analysisSimProofsBase
  loadElimTransferProvenance loadElimOccurrence loadElimDefs
  dfAnalyzeDefs cfgDefs cfgAnalysisProps venomWf venomExecProofs venomInstProps
  sccpCorrectnessProofs simplifyCfgPhiSemantics simplifyCfgPhiRepair
  simplifyCfgStruct finite_map list rich_list

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

Theorem le_occ_step_static:
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\ MEM (StepOcc bb n fuel u t) es ==>
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  n < LENGTH bb.bb_instructions /\
  (EL n bb.bb_instructions).inst_opcode <> PHI
Proof
  strip_tac >>
  `le_occ_valid C fn (StepOcc bb n fuel u t)` by
    metis_tac[le_occ_prefix_member] >>
  fs[le_occ_valid_def] >>
  `bb.bb_label = u.vs_current_bb` by metis_tac[lookup_block_label] >>
  `?before. le_occ_prefix C fn s0 before (EL n bb.bb_instructions) u /\
    (!e. MEM e before ==> MEM e es)` by
    metis_tac[le_occ_prefix_step_before] >>
  `le_occ_route before <> [] /\ is_fn_path fn (le_occ_route before) /\
    HD (le_occ_route before) = s0.vs_current_bb /\
    LAST (le_occ_route before) = u.vs_current_bb` by
    metis_tac[le_occ_prefix_route] >>
  `fn_reachable fn bb.bb_label` by
    (irule scfg_path_member_reachable >> qexists `le_occ_route before` >>
     simp[] >> metis_tac[LAST_MEM]) >>
  metis_tac[lookup_block_MEM, step_inst_ok_imp_not_phi]
QED

Theorem le_occ_route_phi_member[local]:
  !es. MEM (PhiOcc bb u t) es ==> MEM bb.bb_label (le_occ_route es)
Proof
  Induct >> simp[le_occ_route_def] >> Cases_on `h` >>
  simp[le_occ_route_def] >> metis_tac[]
QED

Theorem le_occ_phi_static:
  wf_function fn /\ fn_inst_wf fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\ MEM (PhiOcc bb u t) es ==>
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label
Proof
  strip_tac >>
  `le_occ_valid C fn (PhiOcc bb u t)` by metis_tac[le_occ_prefix_member] >>
  `MEM bb fn.fn_blocks` by
    (fs[le_occ_valid_def] >> metis_tac[lookup_block_MEM]) >>
  drule_all le_occ_prefix_route >> strip_tac >> simp[] >>
  irule scfg_path_member_reachable >> qexists `le_occ_route es` >>
  simp[] >> metis_tac[le_occ_route_phi_member]
QED

Theorem le_retained_occ_value_no_write:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  le_singleton_retained_occ ctx fn key (Var v) e ==>
  v NOTIN le_occ_writes e
Proof
  strip_tac >>
  Cases_on `e`
  >- (drule_all le_occ_step_static >> strip_tac >>
      gvs[le_singleton_retained_occ_def, le_occ_writes_def] >>
      strip_tac >>
      `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
        b.bb_label n)) key <> SOME [Var v]` by
        (irule le_ordinary_definition_value_cut >>
         simp[]) >> gvs[]) >>
  drule_all le_occ_phi_static >> strip_tac >>
  fs[le_singleton_retained_occ_def, le_occ_writes_def] >>
  strip_tac >> fs[le_phi_outputs_def, MEM_FLAT, MEM_MAP] >>
  `MEM i' b.bb_instructions` by
    (fs[le_phi_prefix_take] >> metis_tac[MEM_TAKE]) >>
  `i'.inst_opcode = PHI` by
    (mp_tac (Q.SPEC `b.bb_instructions` phi_prefix_all_phi) >>
     fs[le_phi_prefix_take, EVERY_MEM]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     b.bb_label 0)) key <> SOME [Var v]` by
    (irule le_phi_definition_value_cut >> simp[] >> qexists `i'` >> gvs[]) >>
  gvs[]
QED

Theorem le_retained_occ_key_no_write:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  le_singleton_retained_occ ctx fn (LK_Op (Var a)) op e ==>
  a NOTIN le_occ_writes e
Proof
  strip_tac >>
  Cases_on `e`
  >- (drule_all le_occ_step_static >> strip_tac >>
      gvs[le_singleton_retained_occ_def, le_occ_writes_def] >> strip_tac >>
      `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
        b.bb_label n)) (LK_Op (Var a)) = NONE` by
        (irule le_ordinary_definition_key_cut >> simp[]) >> gvs[]) >>
  drule_all le_occ_phi_static >> strip_tac >>
  fs[le_singleton_retained_occ_def, le_occ_writes_def] >>
  strip_tac >> fs[le_phi_outputs_def, MEM_FLAT, MEM_MAP] >>
  `MEM i' b.bb_instructions` by
    (fs[le_phi_prefix_take] >> metis_tac[MEM_TAKE]) >>
  `i'.inst_opcode = PHI` by
    (mp_tac (Q.SPEC `b.bb_instructions` phi_prefix_all_phi) >>
     fs[le_phi_prefix_take, EVERY_MEM]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
     b.bb_label 0)) (LK_Op (Var a)) = NONE` by
    (irule le_phi_definition_key_cut >> simp[] >> qexists `i'` >> gvs[]) >>
  gvs[]
QED

Theorem le_singleton_suffix_value_no_writes:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  EVERY (le_singleton_retained_occ ctx fn key (Var v)) suffix ==>
  EVERY (\q. v NOTIN le_occ_writes q) suffix
Proof
  strip_tac >> simp[EVERY_MEM] >> qx_gen_tac `q` >> strip_tac >>
  `MEM q (pre ++ e::suffix)` by simp[] >>
  `le_singleton_retained_occ ctx fn key (Var v) q` by
    metis_tac[EVERY_MEM] >>
  drule_all le_retained_occ_value_no_write >> simp[]
QED

Theorem le_singleton_suffix_key_no_writes:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  EVERY (le_singleton_retained_occ ctx fn (LK_Op (Var a)) op) suffix ==>
  EVERY (\q. a NOTIN le_occ_writes q) suffix
Proof
  strip_tac >> simp[EVERY_MEM] >> qx_gen_tac `q` >> strip_tac >>
  `MEM q (pre ++ e::suffix)` by simp[] >>
  `le_singleton_retained_occ ctx fn (LK_Op (Var a)) op q` by
    metis_tac[EVERY_MEM] >>
  drule_all le_retained_occ_key_no_write >> simp[]
QED

Theorem le_singleton_suffix_value_lookup:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ StepOcc bb n fuel u t::suffix) i s /\
  EVERY (le_singleton_retained_occ ctx fn key (Var v)) suffix ==>
  lookup_var v s = lookup_var v t
Proof
  strip_tac >> drule_all le_singleton_suffix_value_no_writes >> strip_tac >>
  drule_all le_occ_prefix_suffix_lookup >> simp[le_occ_post_def]
QED

Theorem le_singleton_suffix_key_lookup:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ StepOcc bb n fuel u t::suffix) i s /\
  EVERY (le_singleton_retained_occ ctx fn (LK_Op (Var a)) op) suffix ==>
  lookup_var a s = lookup_var a t
Proof
  strip_tac >> drule_all le_singleton_suffix_key_no_writes >> strip_tac >>
  drule_all le_occ_prefix_suffix_lookup >> simp[le_occ_post_def]
QED

Theorem le_generator_key_output_separate:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  n < LENGTH bb.bb_instructions /\
  le_transfer_generates ctx (EL n bb.bb_instructions) (LK_Op (Var a)) op ==>
  ~MEM a (EL n bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `MEM (EL n bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  drule_all le_generator_key_variable_available >> strip_tac >>
  `ssa_form fn` by metis_tac[le_reachable_ssa_unique] >>
  strip_tac >> fs[def_available_at_def] >>
  `def_inst = EL n bb.bb_instructions` by
    metis_tac[ssa_form_output_unique] >>
  `def_bb = bb` by metis_tac[wf_function_instruction_block] >> gvs[] >>
  `i = n /\ j = n` by
    (conj_tac >> irule inst_ids_el_eq >> qexistsl [`bb`, `fn`] >>
     gvs[wf_function_def] >> metis_tac[]) >> decide_tac
QED
