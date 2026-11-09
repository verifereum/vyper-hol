Theory loadElimStructuralAvailability
Ancestors
  loadElimStructuralCurrentness loadElimReachedAvailability
  loadElimReachedNormalize loadElimSingletonCurrentness loadElimExitCurrentness
  loadElimOccurrence loadElimOperandValidity loadElimDefs
  loadElimActualGeneration loadElimOccurrenceCoverage loadElimSingletonSuffix
  loadElimOccurrencePredecessor makeSsaHelper
  loadElimAbsoluteKey loadElimKeyRead loadElimKeyReadOperational
  venomExecSemantics venomState venomInst finite_map list rich_list venomWf

Theorem le_occ_prefix_singleton_current_structural:
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
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand op s
Proof
  strip_tac >> irule le_occ_prefix_singleton_current_local >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `s0`] >> simp[] >>
  metis_tac[le_occ_step_operands_valid]
QED

Theorem le_frame_singleton_current_structural:
  frame_reach C fn s0 i s /\
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand op s
Proof
  strip_tac >> drule_all le_occ_prefix_annotate >> strip_tac >>
  irule le_occ_prefix_singleton_current_structural >>
  metis_tac[]
QED

Theorem le_occ_prefix_exit_singleton_current_structural:
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
  is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\ ~u.vs_halted /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) s.vs_current_bb)) key = SOME [op] ==>
  le_key_read ctx.lctx_addr_space key u = eval_operand op u
Proof
  strip_tac >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_terminator_end >> strip_tac >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb (LENGTH bb.bb_instructions))) key = SOME [op]` by
    (irule le_analyze_singleton_exit >> simp[] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb s.vs_inst_idx)) key = SOME [op]` by
    (`FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
        s.vs_current_bb s.vs_inst_idx)) key = SOME [op] \/
      le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op` by
       (irule le_analyze_singleton_step >> simp[] >> metis_tac[]) >>
     metis_tac[le_configured_terminator_no_generation]) >>
  `le_key_read ctx.lctx_addr_space key s = eval_operand op s` by
    (irule le_occ_prefix_singleton_current_structural >> simp[] >>
     qexistsl [`C`, `es`, `fn`, `i`, `s0`] >> simp[] >> metis_tac[]) >>
  metis_tac[le_terminator_key_read, le_terminator_operand]
QED

Theorem le_occ_prefix_exit_var_current_structural:
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
  is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\ ~u.vs_halted /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) s.vs_current_bb)) key = SOME [Var v] ==>
  le_key_read ctx.lctx_addr_space key u = lookup_var v u
Proof
  strip_tac >> drule_all le_occ_prefix_exit_singleton_current_structural >>
  simp[eval_operand_def]
QED

Theorem le_occ_prefix_singleton_available_structural:
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
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [op] ==>
  ?w. eval_operand op s = SOME w
Proof
  strip_tac >>
  drule_all le_occ_prefix_singleton_suffix >> strip_tac >>
  qpat_x_assum `es = _` SUBST_ALL_TAC >>
  `le_occ_valid C fn (StepOcc bb n fuel u t)` by
    (irule le_occ_prefix_member >> metis_tac[MEM_APPEND, MEM]) >>
  `step_inst fuel C (EL n bb.bb_instructions) u = OK t` by
    fs[le_occ_valid_def] >>
  `?w. eval_operand op t = SOME w` by
    metis_tac[le_configured_generation_available] >>
  `!v. op = Var v ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    (rpt strip_tac >> qpat_x_assum `op = _` SUBST_ALL_TAC >>
     drule_all le_singleton_suffix_value_no_writes >> simp[]) >>
  `le_absolute_key ctx.lctx_addr_space (LK_Op op)` by simp[le_absolute_key_def] >>
  `!v. LK_Op op = LK_Op (Var v) ==> EVERY (\q. v NOTIN le_occ_writes q) suffix` by
    simp[] >>
  `le_key_address ctx.lctx_addr_space (LK_Op op) s =
    le_key_address ctx.lctx_addr_space (LK_Op op) t` by
    (drule_all le_prefix_suffix_key_address >> simp[le_occ_post_def]) >>
  metis_tac[le_key_address_operand_injective]
QED

Theorem le_occ_prefix_exit_singleton_value_structural:
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
  is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\ ~u.vs_halted /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) s.vs_current_bb)) key = SOME [op] ==>
  ?w. le_key_read ctx.lctx_addr_space key u = SOME w /\ eval_operand op u = SOME w
Proof
  strip_tac >>
  `le_key_read ctx.lctx_addr_space key u = eval_operand op u` by
    (irule le_occ_prefix_exit_singleton_current_structural >> simp[] >>
     qexistsl [`C`, `es`, `fn`, `i`, `k`, `s`, `s0`] >> simp[] >> metis_tac[]) >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  drule_all le_active_terminator_end >> strip_tac >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[le_occ_prefix_dfs] >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb (LENGTH bb.bb_instructions))) key = SOME [op]` by
    (irule le_analyze_singleton_exit >> simp[] >> metis_tac[]) >>
  `FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
    s.vs_current_bb s.vs_inst_idx)) key = SOME [op]` by
    (`FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
        s.vs_current_bb s.vs_inst_idx)) key = SOME [op] \/
      le_transfer_generates ctx (EL s.vs_inst_idx bb.bb_instructions) key op` by
       (irule le_analyze_singleton_step >> simp[] >> metis_tac[]) >>
     metis_tac[le_configured_terminator_no_generation]) >>
  `?w. eval_operand op s = SOME w` by
    (irule le_occ_prefix_singleton_available_structural >> simp[] >>
     qexistsl [`C`, `ctx`, `es`, `fn`, `i`, `key`, `s0`] >> simp[] >> metis_tac[]) >>
  metis_tac[le_terminator_operand]
QED

Theorem le_occ_prefix_phi_selected_value_structural:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
  pre <> [] /\
  compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key lbl inst = SOME pa /\
  bb.bb_label = pa.pa_join_lbl /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) ==>
  ?front prev j t k pairs v w.
    pre = front ++ [StepOcc prev t.vs_inst_idx k t u] /\
    le_occ_prefix C fn s0 front j t /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME prev /\
    is_terminator j.inst_opcode /\ step_inst k C j t = OK u /\
    ~u.vs_halted /\ u.vs_prev_bb = SOME prev.bb_label /\
    MEM prev.bb_label (cfg_preds_of (cfg_analyze fn) bb.bb_label) /\
    pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
    MAP FST pairs = cfg_preds_of (cfg_analyze fn) pa.pa_join_lbl /\
    MEM (prev.bb_label,v) pairs /\
    FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) prev.bb_label))
      key = SOME [Var v] /\
    lookup_var v u = SOME w /\ le_key_read ctx.lctx_addr_space key u = SOME w
Proof
  strip_tac >> drule_all le_occ_prefix_phi_selected >> strip_tac >>
  `prev.bb_label = t.vs_current_bb` by metis_tac[lookup_block_label] >>
  `?w. le_key_read ctx.lctx_addr_space key u = SOME w /\
       eval_operand (Var v) u = SOME w` by
    (irule le_occ_prefix_exit_singleton_value_structural >> metis_tac[]) >>
  fs[eval_operand_def] >> metis_tac[]
QED
