Theory fnPlanLineageNativeTerminal
Ancestors
  fnPlanLineageNativeResources fnPlanLineageEntryProduction
  fnPlanLineageInventory fnPlanLineageLiveness fnPlanLineageCallers
  fnPlanLineageNativeTargets
  stackPlanGen venomWf venomInst codegenReadyCompute list rich_list finite_map

Theorem native_terminal_jmp_target_available:
  !fn bb ps targets.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    (!w. MEM w (live_vars_at (liveness_analyze fn) bb.bb_label
      (PRE (LENGTH bb.bb_instructions))) ==>
      MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) /\
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
  metis_tac[]
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
    (rpt strip_tac >> irule native_terminal_jmp_target_available >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb`,`fn`] >> gvs[native_live_boundary_def]) >>
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
  drule_all initialized_entry_preterminal >> strip_tac >>
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

Theorem native_terminal_jmp_live_boundary:
  !fn bb dfg ps ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) ps /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) ==>
    native_live_boundary fn bb (LENGTH bb.bb_instructions) qs
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
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (PRE (LENGTH bb.bb_instructions)))` by
    (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (LAST bb.bb_instructions)`
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`) jmp_no_target_state >>
      simp[] >> strip_tac >> gvs[] >>
      simp_tac bool_ss [native_live_boundary_def] >> conj_tac
      >- (gvs[native_live_boundary_def, release_dead_spills_stack,
              release_dead_spills_domain, MEM_MAP] >> metis_tac[]) >>
      rpt strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
      irule_at Any release_dead_spills_resource_nonincrease >>
      gvs[native_live_boundary_def] >> metis_tac[]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))) = set targets` by
    (drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_set >> simp[]) >>
  `!v. LIST_ELEM_COUNT (Var v) targets <= 1` by
    (gen_tac >> Cases_on `lookup_block succ fn.fn_blocks`
     >- gvs[join_target_ops_def] >>
     drule_at (Pat `join_target_ops _ _ _ _ = _`) ready_join_target_count_le_one >> simp[]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)) ==>
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1` by
    (gvs[native_live_boundary_def] >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_inst_plan_jmp_live_terminal >> simp[] >> strip_tac >>
  simp_tac bool_ss [native_live_boundary_def] >> conj_tac
  >- (rpt strip_tac >>
      `MEM (Var v) targets` by
        (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
      metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
  simp[]
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
  `native_live_boundary fn bb (PRE (LENGTH bb.bb_instructions)) ps` by
    gvs[entry_boundary_resources_def, native_live_boundary_def] >>
  drule_all native_terminal_jmp_live_boundary >> disch_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_terminal_jmp_variable_origins >> simp[] >> disch_tac >>
  simp_tac bool_ss [entry_boundary_resources_def] >> conj_tac
  >- (gvs[entry_boundary_resources_def, prefix_inventory_origins_def] >>
      rpt strip_tac >> metis_tac[]) >>
  gvs[native_live_boundary_def]
QED

Theorem initialized_entry_exit_resources:
  !fn dfg ch growth spill_base lbl_ctr ops qs.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops,qs) ==>
    entry_boundary_resources fn (HD fn.fn_blocks)
      (LENGTH (HD fn.fn_blocks).bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all initialized_entry_preterminal >> strip_tac >>
  drule_all ready_entry_static_boundary >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `(HD fn.fn_blocks).bb_instructions <> []` by metis_tac[bb_well_formed_def] >>
  Cases_on `(LAST (HD fn.fn_blocks).bb_instructions).inst_opcode = JMP`
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        native_terminal_jmp_boundary_step >> simp[]) >>
  `SUC (PRE (LENGTH (HD fn.fn_blocks).bb_instructions)) =
    LENGTH (HD fn.fn_blocks).bb_instructions /\
    PRE (LENGTH (HD fn.fn_blocks).bb_instructions) <
    LENGTH (HD fn.fn_blocks).bb_instructions` by
    (Cases_on `(HD fn.fn_blocks).bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH (HD fn.fn_blocks).bb_instructions))
    (HD fn.fn_blocks).bb_instructions = LAST (HD fn.fn_blocks).bb_instructions` by
    metis_tac[LAST_EL] >>
  `~is_param_opcode (LAST (HD fn.fn_blocks).bb_instructions).inst_opcode /\
    (LAST (HD fn.fn_blocks).bb_instructions).inst_opcode <> PHI` by
    (qpat_x_assum `bb_well_formed _` mp_tac >>
     simp_tac bool_ss [bb_well_formed_def] >> strip_tac >>
     qpat_x_assum `is_terminator _` mp_tac >>
     Cases_on `(LAST (HD fn.fn_blocks).bb_instructions).inst_opcode` >>
     simp_tac (srw_ss()) [is_terminator_def, is_param_opcode_def]) >>
  drule_at (Pat `entry_boundary_resources _ _ _ _`)
    (INST_TYPE [alpha |-> ``:cfg_analysis``] entry_inst_boundary_step) >>
  simp[] >> disch_then drule >> simp[]
QED

Theorem initialized_entry_exit_origins:
  !fn dfg ch growth spill_base lbl_ctr ops qs.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops,qs) ==>
    prefix_inventory_origins (HD fn.fn_blocks)
      (LENGTH (HD fn.fn_blocks).bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all initialized_entry_exit_resources >> simp[entry_boundary_resources_def]
QED

Theorem initialized_entry_exit_live_boundary:
  !fn dfg ch growth spill_base lbl_ctr ops qs.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops,qs) ==>
    native_live_boundary fn (HD fn.fn_blocks)
      (LENGTH (HD fn.fn_blocks).bb_instructions) qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all initialized_entry_exit_resources >>
  simp[entry_boundary_resources_def, native_live_boundary_def]
QED

Theorem ready_join_target_ops_distinct:
  !fn cur inst targets.
    codegen_ready_fn fn /\
    join_target_ops (liveness_analyze fn) fn cur inst = SOME targets ==>
    ALL_DISTINCT targets
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `join_target_ops _ _ _ _ = _` mp_tac >>
  simp[join_target_ops_def, AllCaseEqs()] >> strip_tac >>
  `MEM target_bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `phi_uses_disjoint (collect_phis target_bb.bb_instructions)` by
    metis_tac[fnPlanLineagePhiClassesTheory.ready_block_phi_uses_disjoint] >>
  `ALL_DISTINCT (live_vars_at (liveness_analyze fn) target 0)` by
    metis_tac[fnPlanLineageDistinctTheory.ready_live_vars_at_distinct] >>
  `ALL_DISTINCT (input_vars_from cur target_bb.bb_instructions
    (live_vars_at (liveness_analyze fn) target 0))` by
    metis_tac[fnPlanLineagePhiMapsTheory.input_vars_from_distinct] >>
  gvs[] >> irule listTheory.ALL_DISTINCT_MAP_INJ >> simp[]
QED
