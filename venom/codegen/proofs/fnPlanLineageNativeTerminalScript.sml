Theory fnPlanLineageNativeTerminal
Ancestors
  fnPlanLineageNativeResources fnPlanLineageEntryProduction
  fnPlanLineageInventory fnPlanLineageLiveness fnPlanLineageCallers
  fnPlanLineageNativeTargets
  stackPlanGen venomWf venomInst codegenReadyCompute list rich_list finite_map

Theorem native_terminal_jmp_target_set:
  !fn bb targets.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (LAST bb.bb_instructions) = SOME targets ==>
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions))) = set targets
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
  simp[LIST_TO_SET_MAP]
QED

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
  drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_set >>
  simp[] >> disch_tac >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions /\
    PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  rpt strip_tac >>
  `MEM at (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)))` by gvs[pred_setTheory.EXTENSION] >>
  gvs[MEM_MAP] >>
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

Theorem initialized_entry_jmp_origins:
  !fn dfg ch growth spill_base lbl_ctr ops qs.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    (LAST (HD fn.fn_blocks).bb_instructions).inst_opcode = JMP /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops,qs) ==>
    prefix_inventory_origins (HD fn.fn_blocks)
      (LENGTH (HD fn.fn_blocks).bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all initialized_entry_jmp_preterminal >> strip_tac >>
  drule_all ready_entry_static_boundary >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `(HD fn.fn_blocks).bb_instructions <> []` by metis_tac[bb_well_formed_def] >>
  `native_live_boundary fn (HD fn.fn_blocks)
    (PRE (LENGTH (HD fn.fn_blocks).bb_instructions)) before` by
    gvs[entry_boundary_resources_def, native_live_boundary_def] >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_terminal_jmp_variable_origins >> simp[] >> disch_tac >>
  simp_tac bool_ss [prefix_inventory_origins_def] >> rpt strip_tac >>
  `MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled` by metis_tac[] >>
  `?j. j < PRE (LENGTH (HD fn.fn_blocks).bb_instructions) /\
    j < LENGTH (HD fn.fn_blocks).bb_instructions /\
    MEM v (EL j (HD fn.fn_blocks).bb_instructions).inst_outputs` by
    (gvs[entry_boundary_resources_def, prefix_inventory_origins_def] >> metis_tac[]) >>
  qexists_tac `j` >> simp[]
QED

Theorem native_terminal_jmp_boundary_step:
  !fn bb dfg ps ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    entry_boundary_resources fn bb (PRE (LENGTH bb.bb_instructions)) ps /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) ==>
    entry_boundary_resources fn bb (LENGTH bb.bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions /\
    PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (LAST bb.bb_instructions)`
  >- (drule_at (Pat `entry_boundary_resources _ _ _ _`)
        (INST_TYPE [alpha |-> ``:cfg_analysis``] entry_jmp_no_target_boundary_step) >>
      simp[] >> disch_then drule >> simp[]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))) = set targets` by
    (drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_set >> simp[]) >>
  `!v. LIST_ELEM_COUNT (Var v) targets <= 1` by
    (gen_tac >> Cases_on `lookup_block succ fn.fn_blocks`
     >- gvs[join_target_ops_def] >>
     drule_at (Pat `join_target_ops _ _ _ _ = _`) ready_join_target_count_le_one >> simp[]) >>
  drule_at (Pat `entry_boundary_resources _ _ _ _`)
    (INST_TYPE [alpha |-> ``:cfg_analysis``] entry_jmp_live_terminal) >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  `native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) ps` by
    gvs[entry_boundary_resources_def, native_live_boundary_def] >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_terminal_jmp_variable_origins >> simp[] >> disch_tac >>
  simp_tac bool_ss [entry_boundary_resources_def] >> conj_tac
  >- (gvs[entry_boundary_resources_def, prefix_inventory_origins_def] >>
      rpt strip_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `MEM (Var v) targets` by
        (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
      `0 < LIST_ELEM_COUNT (Var v) qs.ps_stack` by
        metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF] >>
      metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
  simp[]
QED
