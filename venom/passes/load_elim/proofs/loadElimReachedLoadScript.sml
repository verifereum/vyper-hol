Theory loadElimReachedLoad
Ancestors
  loadElimReachedStore loadElimReachedSourceAgreement loadElimSingletonCurrentness
  loadElimOccurrenceInvariants loadElimReplacementSound loadElimAbsoluteKey
  loadElimLatestRead loadElimStructuralAvailability loadElimReachedNormalize
  loadElimOccurrence
  loadElimDefs loadElimKeyRead loadElimGenerationSound loadElimKeyShapeInvariant
  venomWf venomState venomExecSemantics dfgCorrectnessProof
  basePtrDefs memoryCopyElisionSound finite_map list pred_set stateFrame

Theorem le_configured_load_shape:
  le_configured_context ctx /\ i.inst_opcode = ctx.lctx_config.lc_load /\
  inst_wf i ==>
  ?addr out. i.inst_operands = [addr] /\ i.inst_outputs = [out]
Proof
  strip_tac >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def,
      inst_wf_def, LENGTH_EQ_NUM_compute]
QED

Theorem le_configured_load_word:
  le_configured_context ctx /\ i.inst_opcode = ctx.lctx_config.lc_load /\
  i.inst_operands = [addr] /\ i.inst_outputs = [out] /\
  step_inst k C i s = OK s' ==>
  ?a w. eval_operand addr s = SOME a /\
        le_read_address ctx.lctx_addr_space (w2n a) s = SOME w
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def] >>
  simp[Once step_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
       AllCaseEqs()] >> strip_tac >> gvs[le_read_address_def] >> metis_tac[]
QED

Theorem le_empty_configured_load_address:
  le_configured_context ctx /\ i.inst_opcode = ctx.lctx_config.lc_load /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  dfg_assigns_sound ctx.lctx_dfg s /\ i.inst_operands = [addr] /\
  eval_operand addr s = SOME a ==>
  le_key_address ctx.lctx_addr_space
    (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s = SOME (w2n a)
Proof
  strip_tac >>
  `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s = SOME a` by
    metis_tac[normalize_operand_eval_proof] >>
  Cases_on `i.inst_opcode = DLOAD`
  >- (gvs[le_configured_context_def, memory_config_def, storage_config_def,
           transient_config_def, dload_config_def, calldataload_config_def] >>
      simp[load_get_read_key_def, use_memloc_for_read_def, le_key_address_def]) >>
  irule le_empty_read_key_address >> simp[] >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def]
QED

Theorem le_reached_singleton_load_replacement:
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
  DISJOINT G (set (fn_all_vars fn)) /\
  i.inst_opcode = ctx.lctx_config.lc_load /\ inst_wf i /\
  padded_exec_equiv G s t /\
  step_inst k C i s = OK s' /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx))
    (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) = SOME [op] ==>
  ?t'. step_inst k C (load_elim_inst ctx actions
         (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
       padded_exec_equiv G s' t' /\
       s'.vs_current_bb = s.vs_current_bb /\
       s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
       t'.vs_current_bb = t.vs_current_bb /\
       t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >> drule_all le_configured_load_shape >> strip_tac >>
  drule_all le_configured_load_word >> strip_tac >>
  `i.inst_opcode <> PHI` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
        transient_config_def, dload_config_def, calldataload_config_def] >>
  `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s =
     eval_operand addr s` by
    (qpat_assum `ctx.lctx_dfg = _` (fn th => pure_rewrite_tac[th]) >>
     irule le_frame_use_normalize_eval >>
     metis_tac[le_occ_prefix_forget, MEM]) >>
  `le_key_address ctx.lctx_addr_space
    (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s = SOME (w2n a)` by
    (Cases_on `i.inst_opcode = DLOAD`
     >- (gvs[le_configured_context_def, memory_config_def, storage_config_def,
             transient_config_def, dload_config_def, calldataload_config_def] >>
         simp[load_get_read_key_def, use_memloc_for_read_def, le_key_address_def]) >>
     irule le_empty_read_key_address >> simp[] >>
     gvs[le_configured_context_def, memory_config_def, storage_config_def,
         transient_config_def, dload_config_def, calldataload_config_def]) >>
  `le_key_read ctx.lctx_addr_space
    (load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s = SOME w` by
    simp[le_key_read_def] >>
  `eval_operand op s = SOME w` by
    (drule_all le_occ_prefix_singleton_current_structural >> metis_tac[]) >>
  `eval_operand op t = SOME w` by
    (Cases_on `op` >> fs[eval_operand_def, Excl "isPREFIX"]
     >~ [`lookup_var v t = SOME w`]
     >- (`MEM v (fn_all_vars fn)` by
            (irule le_occ_prefix_singleton_source_var >> metis_tac[]) >>
         fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
            loadElimMemoryRelTheory.padded_exec_equiv_def,
            Excl "isPREFIX"] >> metis_tac[]) >>
     gvs[loadElimMemoryRelTheory.padded_exec_equiv_def, execution_frame_def]) >>
  `i.inst_opcode <> INVOKE` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
        transient_config_def, dload_config_def, calldataload_config_def] >>
  `load_elim_inst ctx actions
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i =
      mk_assign_inst i op` by gvs[load_elim_inst_def] >>
  simp[Excl "isPREFIX"] >> irule le_configured_load_replacement >>
  simp[Excl "isPREFIX"] >>
  qexists `ctx` >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem le_reached_captured_load_replacement:
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  DISJOINT G (set (fn_all_vars fn)) /\
  i.inst_opcode = ctx.lctx_config.lc_load /\ inst_wf i /\
  padded_exec_equiv G s t /\
  step_inst k C i s = OK s' /\
  key = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
    (normalize_operand ctx.lctx_dfg []) i /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx))
    key = SOME ops /\ 1 < LENGTH ops /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key
    s.vs_current_bb i = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  (!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl) /\
  phi_action_lookup actions i.inst_id = SOME pa.pa_phi_out /\
  le_key_read ctx.lctx_addr_space key u = SOME captured /\
  lookup_var pa.pa_phi_out t = SOME captured ==>
  ?t'. step_inst k C (load_elim_inst ctx actions
         (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
       padded_exec_equiv G s' t' /\
       s'.vs_current_bb = s.vs_current_bb /\
       s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
       t'.vs_current_bb = t.vs_current_bb /\
       t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >> drule_all le_configured_load_shape >> strip_tac >>
  drule_all le_configured_load_word >> strip_tac >>
  `i.inst_opcode <> PHI` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
        transient_config_def, dload_config_def, calldataload_config_def] >>
  `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s =
     eval_operand addr s` by
    (qpat_assum `ctx.lctx_dfg = _` (fn th => pure_rewrite_tac[th]) >>
     irule le_frame_use_normalize_eval >>
     metis_tac[le_occ_prefix_forget, MEM]) >>
  `le_key_read ctx.lctx_addr_space key u =
   le_key_read ctx.lctx_addr_space key s` by
    (drule_all le_occ_latest_join_source_read >> simp[]) >>
  `le_key_address ctx.lctx_addr_space key s = SOME (w2n a)` by
    (gvs[] >> Cases_on `i.inst_opcode = DLOAD`
     >- (gvs[le_configured_context_def, memory_config_def, storage_config_def,
             transient_config_def, dload_config_def, calldataload_config_def] >>
         simp[load_get_read_key_def, use_memloc_for_read_def, le_key_address_def]) >>
     irule le_empty_read_key_address >> simp[] >>
     gvs[le_configured_context_def, memory_config_def, storage_config_def,
         transient_config_def, dload_config_def, calldataload_config_def]) >>
  `le_key_read ctx.lctx_addr_space key s = SOME w` by
    simp[le_key_read_def] >>
  `eval_operand (Var pa.pa_phi_out) t = SOME w` by
    gvs[eval_operand_def] >>
  `i.inst_opcode <> INVOKE` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
        transient_config_def, dload_config_def, calldataload_config_def] >>
  `load_elim_inst ctx actions
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i =
      mk_assign_inst i (Var pa.pa_phi_out)` by
    (Cases_on `ops` >> gvs[load_elim_inst_def] >>
     Cases_on `t'` >> gvs[]) >>
  simp[Excl "isPREFIX"] >> irule le_configured_load_replacement >>
  simp[Excl "isPREFIX"] >>
  qexists `ctx` >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED
