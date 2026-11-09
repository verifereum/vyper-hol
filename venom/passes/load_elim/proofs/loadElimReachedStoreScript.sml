Theory loadElimReachedStore
Ancestors
  loadElimOccurrenceInvariants loadElimReplacementSound
  loadElimStructuralCurrentness loadElimReachedNormalize
  loadElimHomogeneousCurrentness loadElimDefs loadElimOccurrence
  loadElimKeyShapeInvariant loadElimKeyRead finite_map
  dfgCorrectnessProof basePtrDefs memoryCopyElisionSound
  dfAnalyzeDefs cfgAnalysis list loadElimAbsoluteKey
  loadElimConfiguredGeneration loadElimGenerationSound venomWf

Theorem le_occ_prefix_frozen_store_test_current:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  dfg_assigns_sound (dfg_build_function fn) s0 /\
  bp_ptr_sound ctx.lctx_bp s0 /\ alloca_inv s0 /\ allocas_in_word s0 /\
  bp_ptrs_bounded ctx.lctx_bp fn s0 /\
  le_step_preserves ctx.lctx_bp (dfg_build_function fn) fn /\
  (!bb u t. MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    eval_phis u bb.bb_instructions = OK t /\
    dfg_assigns_sound (dfg_build_function fn) u ==>
    dfg_assigns_sound (dfg_build_function fn) t) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\
  EVERY (\a. case (a,value) of (Var _,Var _) =>
    normalize_operand ctx.lctx_dfg [] a = normalize_operand ctx.lctx_dfg [] value
    | _ => a = value) vs ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand value s
Proof
  strip_tac >>
  `dfg_assigns_sound (dfg_build_function fn) s /\
   (!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
     dfg_assigns_sound (dfg_build_function fn) u /\
     dfg_assigns_sound (dfg_build_function fn) t)` by
    (irule le_occ_prefix_frozen_dfg >> metis_tac[]) >>
  irule le_occ_prefix_store_test_current >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `s0`, `vs`] >> gvs[] >>
  first_assum ACCEPT_TAC
QED

Theorem le_configured_store_nop_test:
  le_configured_context ctx /\
  ctx.lctx_config.lc_store = SOME i.inst_opcode /\
  load_elim_inst ctx actions ll i = mk_nop_inst i ==>
  ?addr value vs.
    i.inst_operands = [addr; value] /\
    FLOOKUP (unwrap_load_lattice ll)
      (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
        (normalize_operand ctx.lctx_dfg []) i) = SOME vs /\
    vs <> [] /\
    EVERY (\a. case (a,value) of (Var _,Var _) =>
      normalize_operand ctx.lctx_dfg [] a = normalize_operand ctx.lctx_dfg [] value
      | _ => a = value) vs
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> ctx.lctx_config.lc_load /\
   i.inst_opcode <> NOP` by
    gvs[le_configured_context_def, memory_config_def, storage_config_def,
        transient_config_def, dload_config_def, calldataload_config_def] >>
  `i <> mk_nop_inst i` by
    (strip_tac >> pop_assum (mp_tac o AP_TERM ``\j:instruction. j.inst_opcode``) >>
     simp[passSharedDefsTheory.mk_nop_inst_def]) >>
  qpat_x_assum `load_elim_inst _ _ _ _ = _` mp_tac >>
  simp[load_elim_inst_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem le_configured_store_opcode:
  le_configured_context ctx /\ ctx.lctx_config.lc_store = SOME i.inst_opcode ==>
  MEM (i.inst_opcode,ctx.lctx_addr_space)
    [(MSTORE,AddrSp_Memory); (SSTORE,AddrSp_Storage); (TSTORE,AddrSp_Transient)]
Proof
  strip_tac >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def]
QED

Theorem le_configured_store_outputs:
  le_configured_context ctx /\ ctx.lctx_config.lc_store = SOME i.inst_opcode /\
  inst_wf i ==> i.inst_outputs = []
Proof
  strip_tac >> drule_all le_configured_store_opcode >>
  simp[] >> strip_tac >> fs[inst_wf_def]
QED

Theorem le_empty_store_key_read:
  le_configured_context ctx /\ ctx.lctx_config.lc_store = SOME i.inst_opcode /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  dfg_assigns_sound ctx.lctx_dfg s /\
  i.inst_operands = [addr;value] /\ eval_operand addr s = SOME a ==>
  le_key_read ctx.lctx_addr_space
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s =
  le_read_address ctx.lctx_addr_space (w2n a) s
Proof
  strip_tac >> drule_all le_configured_store_opcode >> strip_tac >>
  `eval_operand (normalize_operand ctx.lctx_dfg [] addr) s = SOME a` by
    metis_tac[normalize_operand_eval_proof] >>
  `le_key_address ctx.lctx_addr_space
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s = SOME (w2n a)` by
    (irule le_empty_write_key_address >> metis_tac[]) >>
  simp[le_key_read_def]
QED

Theorem le_reached_store_replacement:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  ctx.lctx_config.lc_store = SOME i.inst_opcode /\ inst_wf i /\
  padded_exec_equiv V s t /\ step_inst k C i s = OK s' /\
  load_elim_inst ctx actions
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i = mk_nop_inst i ==>
  ?t'. step_inst k C (load_elim_inst ctx actions
         (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx) i) t = OK t' /\
       padded_exec_equiv V s' t' /\
       s'.vs_current_bb = s.vs_current_bb /\
       s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
       t'.vs_current_bb = t.vs_current_bb /\
       t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >> drule_all le_configured_store_nop_test >> strip_tac >>
  drule_all le_configured_store_opcode >> strip_tac >>
  drule_all le_configured_store_outputs >> strip_tac >>
  `?a. eval_operand addr s = SOME a` by
    (irule le_generating_store_address_exists >> metis_tac[]) >>
  `?w. eval_operand value s = SOME w` by
    metis_tac[le_generating_store_state] >>
  `i.inst_opcode <> PHI /\ MEM value i.inst_operands /\
   MEM addr i.inst_operands` by gvs[] >>
  `le_key_read ctx.lctx_addr_space
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s = eval_operand value s` by
    (irule le_occ_prefix_store_test_current_structural >> simp[] >>
     qexistsl [`C`, `es`, `fn`, `i`, `s0`, `vs`] >> gvs[] >>
     first_assum ACCEPT_TAC) >>
  `eval_operand (normalize_operand (dfg_build_function fn) [] addr) s =
     eval_operand addr s` by
    (irule le_frame_use_normalize_eval >> metis_tac[le_occ_prefix_forget]) >>
  `le_key_address ctx.lctx_addr_space
    (load_get_write_key ctx.lctx_bp ctx.lctx_addr_space
      (normalize_operand ctx.lctx_dfg []) i) s = SOME (w2n a)` by
    (irule le_empty_write_key_address >> metis_tac[]) >>
  `le_read_address ctx.lctx_addr_space (w2n a) s = SOME w` by
    gvs[le_key_read_def] >>
  simp[] >> irule le_configured_store_replacement >> metis_tac[]
QED
