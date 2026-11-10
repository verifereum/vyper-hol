Theory loadElimLatestRead
Ancestors
  loadElimLatestRetention loadElimSingletonCurrentness loadElimSingletonSuffix
  loadElimReachableSSA loadElimDefinitionCuts loadElimOccurrenceRead loadElimAbsoluteKey
  loadElimKeyRead loadElimKeyShapeInvariant loadElimActualGeneration
  loadElimOccurrence loadElimOccurrenceCoverage analysisSimProofsBase
  loadElimOperationalHistory simplifyCfgPhiSemantics
  loadElimReachedNormalize loadElimOperandValidity loadElimSingletonAvailability
  simplifyCfgPhiRepair venomExecProofs
  loadElimDefs venomExecProps venomWf list rich_list finite_map pred_set words

Theorem le_present_occ_key_no_write:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  (!b n fuel x y. e = StepOcc b n fuel x y ==>
    ?vs. FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
      b.bb_label n)) (LK_Op (Var a)) = SOME vs) /\
  (!b x y. e = PhiOcc b x y ==>
    ?vs. FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
      b.bb_label 0)) (LK_Op (Var a)) = SOME vs) ==>
  a NOTIN le_occ_writes e
Proof
  strip_tac >>
  Cases_on `e`
  >- (drule_all le_occ_step_static >> strip_tac >>
      fs[le_occ_writes_def] >> strip_tac >>
      `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
        b.bb_label n)) (LK_Op (Var a)) = NONE` by
        (irule le_ordinary_definition_key_cut >> simp[]) >> gvs[]) >>
  drule_all le_occ_phi_static >> strip_tac >>
  fs[le_occ_writes_def] >>
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

Theorem le_multivalue_occ_read:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  ctx.lctx_dfg = dfg_build_function fn /\
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\ MEM e es /\
  (!b n fuel x y. e = StepOcc b n fuel x y ==>
    ?vs. 1 < LENGTH vs /\ FLOOKUP (unwrap_load_lattice
      (df_at NONE (load_analyze ctx fn) b.bb_label (SUC n))) key = SOME vs) /\
  le_absolute_key ctx.lctx_addr_space key /\
  le_key_address ctx.lctx_addr_space key (le_occ_pre e) = SOME a /\
  a < dimword (:256) ==>
  le_read_address ctx.lctx_addr_space a (le_occ_after e) =
  le_read_address ctx.lctx_addr_space a (le_occ_pre e)
Proof
  strip_tac >>
  Cases_on `e`
  >- (`le_occ_valid C fn (StepOcc b n n0 v v0)` by
        metis_tac[le_occ_prefix_member] >>
      `MEM b.bb_label (cfg_analyze fn).cfg_dfs_pre` by
        metis_tac[le_occ_step_dfs] >>
      `inst_wf (EL n b.bb_instructions)` by
        metis_tac[le_occ_step_wf] >>
      `df_at NONE (load_analyze ctx fn) b.bb_label (SUC n) =
        load_transfer ctx (EL n b.bb_instructions)
          (df_at NONE (load_analyze ctx fn) b.bb_label n)` by
        (irule le_analyze_step_transfer >> fs[le_occ_valid_def] >>
         metis_tac[lookup_block_label]) >>
      `le_inst_operands_valid ctx.lctx_dfg (EL n b.bb_instructions) v` by
        (drule_all le_occ_prefix_step_before >> strip_tac >>
         drule_all le_occ_step_static >> strip_tac >>
         simp[le_inst_operands_valid_def, EVERY_MEM] >> rpt strip_tac >>
         irule le_frame_use_chain_valid >> metis_tac[le_occ_prefix_forget]) >>
      fs[le_read_address_occ_after, le_occ_pre_def, le_occ_post_def,
         le_occ_valid_def] >>
      irule le_configured_multivalue_step_read_local >> metis_tac[]) >>
  `le_occ_valid C fn (PhiOcc b v v0)` by metis_tac[le_occ_prefix_member] >>
  metis_tac[le_phi_read_occ_after]
QED

Theorem le_capture_retention_source_read:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  (!b n fuel x y. MEM (StepOcc b n fuel x y) (PhiOcc bb u p :: suffix) ==>
    ?vs. 1 < LENGTH vs /\
      FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) b.bb_label n)) key = SOME vs /\
      FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) b.bb_label (SUC n))) key = SOME vs) /\
  (!b x y. MEM (PhiOcc b x y) (PhiOcc bb u p :: suffix) ==>
    ?vs. 1 < LENGTH vs /\
      FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) b.bb_label 0)) key = SOME vs) /\
  le_absolute_key ctx.lctx_addr_space key ==>
  le_key_read ctx.lctx_addr_space key u = le_key_read ctx.lctx_addr_space key s
Proof
  strip_tac >>
  `le_occ_chain u (PhiOcc bb u p :: suffix) s` by
    (drule le_occ_prefix_chain >> simp[le_occ_chain_append, le_occ_chain_def,
       le_occ_pre_def] >> metis_tac[]) >>
  `EVERY (le_occ_valid C fn) (PhiOcc bb u p :: suffix)` by
    (drule le_occ_prefix_valid >> simp[]) >>
  `!v. key = LK_Op (Var v) ==>
    EVERY (\e. v NOTIN le_occ_writes e) (PhiOcc bb u p :: suffix)` by
    (pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >> BETA_TAC >>
     irule le_present_occ_key_no_write >> metis_tac[MEM_APPEND]) >>
  `le_key_address ctx.lctx_addr_space key s =
    le_key_address ctx.lctx_addr_space key u` by
    (irule le_occ_chain_key_address >> metis_tac[]) >>
  Cases_on `le_key_address ctx.lctx_addr_space key u`
  >- gvs[le_key_read_def] >>
  rename1 `le_key_address ctx.lctx_addr_space key u = SOME a` >>
  `a < dimword (:256)` by
    (Cases_on `key` >>
     fs[le_key_address_def, AllCaseEqs()] >> gvs[] >> simp[w2n_lt]) >>
  `EVERY (\e. !a. le_key_address ctx.lctx_addr_space key (le_occ_pre e) = SOME a /\
     a < dimword (:256) ==>
     le_read_address ctx.lctx_addr_space a (le_occ_after e) =
     le_read_address ctx.lctx_addr_space a (le_occ_pre e)) (PhiOcc bb u p :: suffix)` by
    (pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> rpt strip_tac >>
     drule_at_then (Pat `le_occ_prefix _ _ _ _ _ _`) mp_tac le_multivalue_occ_read >>
     disch_then irule >> simp[] >>
     qexists `key` >> simp[] >> metis_tac[]) >>
  `le_read_address ctx.lctx_addr_space a s = le_read_address ctx.lctx_addr_space a u` by
    (irule le_occ_chain_retained_read >> metis_tac[]) >>
  gvs[le_key_read_def]
QED

Theorem le_occ_latest_join_source_read:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key
    s.vs_current_bb i = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  i.inst_opcode = ctx.lctx_config.lc_load /\ i.inst_operands = [addr] /\
  key = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
    (normalize_operand ctx.lctx_dfg []) i /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb s.vs_inst_idx)) key = SOME ops /\ 1 < LENGTH ops /\
  (!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl) ==>
  le_key_read ctx.lctx_addr_space key u = le_key_read ctx.lctx_addr_space key s
Proof
  strip_tac >>
  `le_absolute_key ctx.lctx_addr_space key` by
    (drule_all le_analyze_absolute_keys >>
     simp[le_keys_satisfy_def] >> metis_tac[]) >>
  drule_all le_occ_latest_join_multivalue_retention >> strip_tac >>
  drule_all le_capture_retention_source_read >> simp[]
QED
