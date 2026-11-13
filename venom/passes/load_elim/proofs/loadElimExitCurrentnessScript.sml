Theory loadElimExitCurrentness
Ancestors
  loadElimSingletonCurrentness loadElimNoWriteRead loadElimKeyReadOperational
  loadElimActualGeneration venomExecProofs venomExecSemantics venomInst
  memLocDefs loadElimDefs loadElimKeyRead loadElimKeyShapeInvariant
  loadElimTransferProvenance venomState venomWf loadElimOccurrence list

Theorem le_configured_terminator_no_generation:
  le_configured_context ctx /\ is_terminator inst.inst_opcode ==>
  ~le_transfer_generates ctx inst key op
Proof
  simp[le_configured_context_def] >> strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, le_transfer_generates_def,
       memory_config_def, storage_config_def, transient_config_def,
       dload_config_def, calldataload_config_def]
QED

Theorem le_terminator_operand:
  step_inst fuel C inst s = OK u /\ is_terminator inst.inst_opcode ==>
  eval_operand op u = eval_operand op s
Proof
  strip_tac >> drule_all step_terminator_preserves_vars >> strip_tac >>
  drule step_inst_preserves_labels_always >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def]
QED

Theorem le_terminator_allocas:
  step_inst fuel C inst s = OK u /\ is_terminator inst.inst_opcode ==>
  u.vs_allocas = s.vs_allocas
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_opcode_eqs, jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Theorem le_terminator_key_address:
  step_inst fuel C inst s = OK u /\ is_terminator inst.inst_opcode ==>
  le_key_address space key u = le_key_address space key s
Proof
  strip_tac >>
  `!op. eval_operand op u = eval_operand op s` by
    metis_tac[le_terminator_operand] >>
  drule_all le_terminator_allocas >> strip_tac >>
  Cases_on `key` >> simp[le_key_address_def, memloc_runtime_region_def]
QED

Theorem le_terminator_key_read:
  step_inst fuel C inst s = OK u /\ is_terminator inst.inst_opcode ==>
  le_key_read space key u = le_key_read space key s
Proof
  strip_tac >>
  `le_key_address space key u = le_key_address space key s` by
    metis_tac[le_terminator_key_address] >>
  `!a. le_read_address space a u = le_read_address space a s` by
    (gen_tac >> drule_all le_terminator_mutable_reads >>
     disch_then (qspec_then `a` strip_assume_tac) >>
     drule_all le_terminator_readonly_fields >> strip_tac >>
     Cases_on `space` >> gvs[le_read_address_def]) >>
  simp[le_key_read_def] >>
  Cases_on `le_key_address space key s` >> simp[]
QED

Theorem le_active_terminator_end:
  wf_function fn /\ active_inst fn i s /\ is_terminator i.inst_opcode ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = i /\
    SUC s.vs_inst_idx = LENGTH bb.bb_instructions
Proof
  strip_tac >> drule_all le_active_inst_lookup >> strip_tac >>
  qexists `bb` >> simp[] >>
  `bb_well_formed bb` by
    metis_tac[wf_function_bb_well_formed, lookup_block_MEM] >>
  gvs[bb_well_formed_def] >> metis_tac[]
QED

Theorem le_occ_prefix_exit_singleton_current:
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
    dfg_assigns_sound ctx.lctx_dfg u) /\
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
    (irule le_occ_prefix_singleton_current >> simp[] >>
     qexistsl [`C`, `es`, `fn`, `i`, `s0`] >> simp[] >> metis_tac[]) >>
  metis_tac[le_terminator_key_read, le_terminator_operand]
QED

Theorem le_occ_prefix_exit_var_current:
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
    dfg_assigns_sound ctx.lctx_dfg u) /\
  is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\ ~u.vs_halted /\
  FLOOKUP (unwrap_load_lattice
    (df_boundary NONE (load_analyze ctx fn) s.vs_current_bb)) key = SOME [Var v] ==>
  le_key_read ctx.lctx_addr_space key u = lookup_var v u
Proof
  strip_tac >> drule_all le_occ_prefix_exit_singleton_current >>
  simp[eval_operand_def]
QED
