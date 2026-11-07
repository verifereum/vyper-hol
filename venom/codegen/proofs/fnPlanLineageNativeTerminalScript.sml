Theory fnPlanLineageNativeTerminal
Ancestors
  fnPlanLineageNativeResources fnPlanLineageEntryProduction
  fnPlanLineageInventory fnPlanLineageLiveness fnPlanLineageCallers
  stackPlanGen venomWf venomInst codegenReadyCompute list rich_list finite_map

Theorem native_terminal_jmp_target_available:
  !fn bb ps targets.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) ps /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (LAST bb.bb_instructions) = SOME targets ==>
    !at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[fn_reachable_cfg_analyze] >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  qpat_x_assum `join_target_ops _ _ _ _ = _` mp_tac >>
  simp[join_target_ops_def, AllCaseEqs()] >> strip_tac >>
  `set (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)) =
    set (input_vars_from bb.bb_label target_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule analyzed_live_out_jmp >> simp[]) >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions /\
    PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  `MEM y (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))` by
    gvs[pred_setTheory.EXTENSION] >>
  `MEM y (live_vars_at (liveness_analyze fn) bb.bb_label (PRE (LENGTH bb.bb_instructions)))` by
    (irule analyzed_computed_operand_demand >> simp[] >> disj2_tac >>
     `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions` by decide_tac >>
     asm_rewrite_tac[]) >>
  metis_tac[native_live_boundary_coverage]
QED

Theorem native_terminal_jmp_variable_origins:
  !fn bb dfg ps ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) ps /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (LAST bb.bb_instructions)`
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`) jmp_no_target_state >>
      simp[] >> strip_tac >> gvs[] >>
      metis_tac[release_dead_spills_inventory_subset]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  `!at. MEM at targets ==> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_available >>
     simp[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_inst_plan_jmp_inventory_subset >> simp[] >>
  disch_tac >> metis_tac[]
QED
