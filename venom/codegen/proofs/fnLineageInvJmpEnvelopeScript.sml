Theory fnLineageInvJmpEnvelope
Ancestors fnLineageInvControl fnLineageInvTerminal fnLineageInvActualReplay
  fnPlanLineageLiveness fnPlanLineageSetup stackPlanGen venomWf venomExecProps codegenReadyCompute
  list rich_list pred_set finite_map stackModel stackPlanTypes stackPlanOps asmIR venomEffects reorderSim fnPlanPrefix fnPlanLineageInventory livenessProofs livenessDefs cfgAnalysisProps cfgDefs

Theorem analyzed_jmp_target_end_live:
  !fn bb k targets.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = JMP /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (EL k bb.bb_instructions) = SOME targets ==>
    set targets = set (MAP Var
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))
Proof
  rpt gen_tac >> strip_tac >>
  `SUC k = LENGTH bb.bb_instructions` by metis_tac[analyzed_jmp_terminal_index] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `LAST bb.bb_instructions = EL k bb.bb_instructions` by
    (`k = PRE (LENGTH bb.bb_instructions)` by decide_tac >> simp[LAST_EL]) >>
  gvs[join_target_ops_def, AllCaseEqs()] >>
  drule_all analyzed_live_out_jmp >> strip_tac >>
  gvs[EXTENSION, MEM_MAP] >> metis_tac[]
QED

Theorem restore_reorder_release_weak_envelope:
  !targets live m core ps rops rs qops qs dfg spillbase.
    ALL_DISTINCT targets /\ set targets = set (MAP Var live) /\
    lineage_core m core ps /\ ALL_DISTINCT core /\ EVERY is_var_operand core /\
    DISJOINT (set core) (FDOM ps.ps_spilled) /\
    set core SUBSET set targets /\
    set targets SUBSET set core UNION FDOM ps.ps_spilled /\
    plan_slots_bounded spillbase ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    restore_spilled_plan targets ps = (rops,rs) /\
    reorder_plan dfg targets rs = (qops,qs) ==>
    lineage_inventory (set targets) (release_dead_spills live qs) /\
    ?tail. lineage_core m tail (release_dead_spills live qs) /\
      EVERY is_var_operand tail /\
      residual_budget_wf spillbase [] ((release_dead_spills live qs) with ps_stack := tail)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY is_var_operand targets` by
    (gvs[EVERY_MEM, EXTENSION, MEM_MAP] >> metis_tac[is_var_operand_def]) >>
  drule_all restore_spilled_plan_target_core >> strip_tac >>
  drule_all full_inventory_reorder_plan_preservation >> strip_tac >>
  `(release_dead_spills live qs).ps_spilled = FEMPTY` by
    (simp[GSYM FDOM_EQ_EMPTY, EXTENSION, phi_release_dead_spills_domain] >>
     gvs[DISJOINT_DEF, EXTENSION, MEM_MAP] >> metis_tac[]) >>
  `residual_budget_wf spillbase [] (qs with ps_stack := tail')` by
    (irule residual_budget_wf_canonical >> gvs[lineage_core_def]) >>
  drule residual_budget_wf_release_dead_spills_core >>
  disch_then (qspec_then `live` assume_tac) >>
  conj_tac
  >- (simp[lineage_inventory_def] >> qexistsl_tac [`m`, `tail'`] >>
      gvs[lineage_core_def, release_dead_spills_stack]) >>
  qexists_tac `tail'` >> gvs[lineage_core_def, release_dead_spills_stack]
QED

Theorem native_join_jmp_weak_envelope:
  !liveness dfg cfg fn inst next halt term cur ps targets ops qs m core spillbase.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops liveness fn cur inst = SOME targets /\
    ALL_DISTINCT targets /\ set targets = set (MAP Var next) /\
    lineage_core m core ps /\ ALL_DISTINCT core /\ EVERY is_var_operand core /\
    DISJOINT (set core) (FDOM ps.ps_spilled) /\
    set core SUBSET set targets /\
    set targets SUBSET set core UNION FDOM ps.ps_spilled /\
    plan_slots_bounded spillbase ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    generate_inst_plan liveness dfg cfg fn inst next halt term cur ps = SOME (ops,qs) ==>
    lineage_inventory (set targets) qs /\
    ?tail. lineage_core m tail qs /\ EVERY is_var_operand tail /\
      residual_budget_wf spillbase [] (qs with ps_stack := tail)
Proof
  rpt gen_tac >> strip_tac >>
  `?target. inst.inst_operands = [Label target]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def, venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, emit_input_plan_def, is_label_operand_def,
       is_commutative_def, generate_emit_ops_def, venom_to_evm_name_def] >>
  Cases_on `restore_spilled_plan targets ps` >> simp[] >>
  rename1 `restore_spilled_plan targets ps = (rops,rs)` >>
  Cases_on `reorder_plan dfg targets rs` >> simp[stack_pop_def] >>
  strip_tac >> gvs[] >>
  `set core SUBSET set targets /\
   set targets SUBSET set core UNION FDOM ps.ps_spilled` by ASM_SET_TAC[] >>
  drule_all restore_reorder_release_weak_envelope >> simp[]
QED

Theorem analyzed_jmp_live_identity:
  !fn bb k.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = JMP ==>
    live_vars_at (liveness_analyze fn) bb.bb_label k =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (EL k bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `(EL k bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  `?lab. (EL k bb.bb_instructions).inst_operands = [Label lab]` by
    gvs[inst_wf_def, AllCaseEqs()] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  drule livenessProofsTheory.live_vars_at_transfer >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `k`] mp_tac) >>
  simp[liveness_transfer_def, live_update_def,
       venomInstTheory.inst_uses_def, venomInstTheory.inst_defs_def,
       ordered_inst_uses_def, venomInstTheory.python_stack_operands_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
       venomInstTheory.ir_specific_operand_order_def]
QED

Theorem native_nonjoin_jmp_weak_envelope:
  !lv dfg cfg fn inst next halt term cur ps ops qs m core spillbase lab.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    inst.inst_operands = [Label lab] /\
    join_target_ops lv fn cur inst = NONE /\ lineage_core m core ps /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    set core SUBSET set (MAP Var next) /\
    set (MAP Var next) SUBSET set core UNION FDOM ps.ps_spilled /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) ==>
    lineage_inventory (set (MAP Var next)) qs /\
    ?tail. lineage_core m tail qs /\ residual_budget_wf spillbase [] (qs with ps_stack := tail)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def, venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       get_non_label_operands_def, emit_input_plan_def, is_label_operand_def,
       is_commutative_def, generate_emit_ops_def, venom_to_evm_name_def,
       stack_pop_def] >> strip_tac >> gvs[] >>
  `ps.ps_stack = REPLICATE m dead_stack_marker ++ core` by gvs[lineage_core_def] >>
  drule regular_post_emit_tail_live_inventory >>
  disch_then (qspec_then `spillbase` (qspec_then `[]` mp_tac)) >>
  simp[]
QED

Theorem analyzed_jmp_weak_envelope:
  !fn bb k dfg cfg halt term spillbase ps ops qs m core.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = JMP /\
    lineage_core m core ps /\ EVERY is_var_operand core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) halt term bb.bb_label ps =
      SOME (ops,qs) ==>
    lineage_inventory (set (MAP Var
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) qs /\
    ?tail. lineage_core m tail qs /\ residual_budget_wf spillbase [] (qs with ps_stack := tail)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all analyzed_jmp_live_identity >> strip_tac >>
  `inst_wf (EL k bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `(EL k bb.bb_instructions).inst_outputs = [] /\
   ?lab. (EL k bb.bb_instructions).inst_operands = [Label lab]` by
    gvs[inst_wf_def, AllCaseEqs()] >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))
    SUBSET set core UNION FDOM ps.ps_spilled` by
    (gvs[SUBSET_DEF, MEM_MAP, lineage_core_def, MEM_REPLICATE, MEM_APPEND] >>
     rpt strip_tac >> gvs[dead_stack_marker_def] >> metis_tac[]) >>
  fs[] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (EL k bb.bb_instructions)`
  >- (drule_all native_nonjoin_jmp_weak_envelope >> simp[]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  drule_all analyzed_jmp_target_end_live >> strip_tac >>
  drule_all analyzed_jmp_target_footprint >> strip_tac >>
  drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
  `plan_slots_bounded spillbase ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (fs[residual_budget_wf_def, planSpillBoundsTheory.plan_slots_bounded_def] >>
     metis_tac[]) >>
  `set core SUBSET set targets /\
   set targets SUBSET set core UNION FDOM ps.ps_spilled` by ASM_SET_TAC[] >>
  drule_all native_join_jmp_weak_envelope >> simp[] >> metis_tac[]
QED
