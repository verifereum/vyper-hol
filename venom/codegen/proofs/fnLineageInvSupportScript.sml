Theory fnLineageInvSupport
Ancestors
  venomExecProps rich_list fnPlanLineageEdge fnPlanLineageLiveness planWfMarked fnPlanPrefix fnPlanLineageInventory fnPlanLineageSuffix fnPlanLineageCallers fnPlanLineagePath fnPlanLineageSetup fnPlanLineageDemand livenessProofs cfgAnalysisProps venomWf
  stackPlanTypes stackModel stackPlanGen asmIR venomInst passSharedDefs codegenReadyCompute unitShapeDefs list pred_set

Theorem inst_uses_compute_operands_nonlog:
  !inst v. inst.inst_opcode <> LOG /\ MEM v (inst_uses inst) ==>
    MEM (Var v) (compute_operands inst)
Proof
  rpt gen_tac >>
  simp[compute_operands_def, inst_uses_def, MEM_operand_vars_eq_Var] >>
  IF_CASES_TAC
  >- simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  simp[]
QED

Theorem analyzed_nonlog_live_upper_support:
  !fn bb i.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> LOG ==>
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label i)) SUBSET
    set (MAP Var (venomInst$operand_vars (stackPlanGen$compute_operands (EL i bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >> simp[]) >>
  simp[SUBSET_DEF, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
      MEM_FILTER, MEM_APPEND] >>
  drule_all inst_uses_compute_operands_nonlog >>
  rewrite_tac[GSYM MEM_operand_vars_eq_Var] >>
  strip_tac >> metis_tac[]
QED

Theorem inst_uses_compute_operands_log:
  !inst v. inst_wf inst /\ inst.inst_opcode = LOG /\ MEM v (inst_uses inst) ==>
    MEM (Var v) (stackPlanGen$compute_operands inst)
Proof
  rpt gen_tac >> strip_tac >>
  `?tc rest. inst.inst_operands = Lit tc :: rest` by
    (gvs[inst_wf_def] >> metis_tac[]) >>
  gvs[compute_operands_def, inst_uses_def, MEM_operand_vars_eq_Var]
QED

Theorem analyzed_log_live_upper_support:
  !fn bb i.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = LOG ==>
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label i)) SUBSET
    set (MAP Var (venomInst$operand_vars (stackPlanGen$compute_operands (EL i bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >> simp[]) >>
  simp[SUBSET_DEF, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
      MEM_FILTER, MEM_APPEND] >>
  drule_all inst_uses_compute_operands_log >>
  rewrite_tac[GSYM MEM_operand_vars_eq_Var] >>
  strip_tac >> metis_tac[]
QED

Theorem analyzed_compute_operands_no_marker:
  !fn bb i. codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions ==>
    EVERY (\op. op <> dead_stack_marker)
      (compute_operands (EL i bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >>
  drule codegen_ready_fn_no_marker >>
  simp[EVERY_MEM] >> strip_tac >>
  `EVERY (\op. op <> dead_stack_marker)
     (EL i bb.bb_instructions).inst_operands` by
    (simp[EVERY_MEM] >> metis_tac[EL_MEM]) >>
  simp[compute_operands_def] >> IF_CASES_TAC
  >- (gvs[asmIRTheory.get_non_label_operands_def, EVERY_MEM, MEM_FILTER] >>
      metis_tac[]) >>
  IF_CASES_TAC
  >- (Cases_on `(EL i bb.bb_instructions).inst_operands` >> gvs[EVERY_MEM]) >>
  gvs[EVERY_MEM]
QED

Theorem analyzed_ordinary_live_inventory:
  !fn bb i dfg cfg term lbl ps m core base ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    set core UNION FDOM ps.ps_spilled SUBSET
      set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label i)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      demand_available fn bb i v) /\
    generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) F term lbl ps = (ops,qs)
    ==>
    lineage_inventory (set (MAP Var
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))) qs /\
    ?rest. lineage_core m rest qs /\
      residual_budget_wf base [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\op. op <> dead_stack_marker)
     (compute_operands (EL i bb.bb_instructions))` by
    metis_tac[analyzed_compute_operands_no_marker] >>
  `ssa_form fn /\ wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL i bb.bb_instructions).inst_outputs` by
    metis_tac[codegen_ready_inst_outputs_distinct] >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[analyzed_computed_operand_demand] >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  drule_all definition_support_output_fresh >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) (compute_operands (EL i bb.bb_instructions)) /\
     ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled)
     (EL i bb.bb_instructions).inst_outputs` by
    (gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label i)) SUBSET
    set (MAP Var (venomInst$operand_vars (compute_operands (EL i bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))` by
    (Cases_on `(EL i bb.bb_instructions).inst_opcode = LOG`
     >- (irule analyzed_log_live_upper_support >> simp[]) >>
     irule analyzed_nonlog_live_upper_support >> simp[]) >>
  irule native_regular_live_inventory >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `core` >> asm_rewrite_tac[] >>
  irule SUBSET_TRANS >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `_ SUBSET set (MAP Var (_ ++ _))` mp_tac >>
  simp[SUBSET_DEF, MEM_MAP, reorderSimTheory.input_mem_operand_vars,
    MEM_operand_vars_eq_Var]
QED

Theorem analyzed_suffix_inventory_demand:
  !fn bb i ps m core.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    fn_reachable fn bb.bb_label /\ i <= LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP i bb.bb_instructions) /\
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    set core UNION FDOM ps.ps_spilled SUBSET
      set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label i)) ==>
    !v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      demand_available fn bb i v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all analyzed_ordinary_suffix_demand >>
  simp[EVERY_MEM] >> strip_tac >>
  gvs[SUBSET_DEF, MEM_MAP, MEM_APPEND, dead_stack_marker_def] >>
  rpt strip_tac >> first_x_assum irule >>
  first_x_assum drule >> simp[]
QED

Theorem native_join_jmp_inventory_subset:
  !liveness dfg cfg fn inst next halt term cur ps targets ops qs.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops liveness fn cur inst = SOME targets /\
    pending_inventory_wf targets ps /\
    generate_inst_plan liveness dfg cfg fn inst next halt term cur ps =
      SOME (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `?target. inst.inst_operands = [Label target]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       venomInstTheory.is_param_opcode_def] >>
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  Cases_on `restore_spilled_plan targets ps` >> simp[] >>
  rename1 `restore_spilled_plan targets ps = (rOps,psR)` >>
  Cases_on `reorder_plan dfg targets psR` >> simp[stack_pop_def] >>
  strip_tac >> gvs[] >>
  `!at. MEM at r.ps_stack \/ at IN FDOM r.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    metis_tac[restore_reorder_inventory_subset] >>
  metis_tac[fnPlanLineageInventoryTheory.release_dead_spills_inventory_subset]
QED

Theorem native_join_jmp_support:
  !liveness dfg cfg fn inst next halt term cur ps targets ops qs.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops liveness fn cur inst = SOME targets /\
    pending_inventory_wf targets ps /\
    set targets = set (MAP Var next) /\
    (!op. (MEM op ps.ps_stack /\ op <> dead_stack_marker) \/
          op IN FDOM ps.ps_spilled ==> MEM op targets) /\
    generate_inst_plan liveness dfg cfg fn inst next halt term cur ps =
      SOME (ops,qs) ==>
    qs.ps_spilled = FEMPTY /\
    (!op. (MEM op qs.ps_stack /\ op <> dead_stack_marker) \/
          op IN FDOM qs.ps_spilled ==> MEM op targets) /\
    (!v. MEM v next ==> MEM (Var v) qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `?succ. inst.inst_operands = [Label succ]` by
    (gvs[join_target_ops_def, AllCaseEqs()] >> metis_tac[]) >>
  `qs.ps_spilled = FEMPTY` by
    (irule phi_jmp_plan_spills_empty >>
     goal_assum (drule_at Any) >> simp[] >>
     gvs[EXTENSION, MEM_MAP] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
        metis_tac[native_join_jmp_inventory_subset] >>
      gvs[EXTENSION] >> metis_tac[]) >>
  drule_all generate_inst_plan_jmp_suffix >> strip_tac >>
  gvs[EXTENSION, MEM_MAP, MEM_APPEND] >> metis_tac[]
QED

Theorem native_parameter_wf_marked:
  !fn ch growth spill_base lbl_ctr.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    generated_plan_state_wf_marked spill_base
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_parameter_names_distinct >> strip_tac >>
  simp[prepare_params_plan_def] >> IF_CASES_TAC
  >- simp[initial_cleanup_wf_marked] >>
  simp[parameter_push_fold] >>
  qmatch_goalsub_abbrev_tac `popmany_plan dead pushed` >>
  `generated_plan_state_wf_marked spill_base pushed` by
    (simp[Abbr `pushed`, init_cleanup_plan_state_def, init_plan_state_def,
       generated_plan_state_wf_marked_def,
       planSpillBoundsTheory.plan_slots_bounded_def,
       planSpillBoundsTheory.alloc_slots_bounded_def,
       doSwapSimTheory.spill_alloc_layout_wf_def, init_spill_alloc_def] >>
     irule FILTER_ALL_DISTINCT >>
     `MAP (\inst. Var (HD inst.inst_outputs))
       (get_params (HD fn.fn_blocks).bb_instructions) =
       MAP Var (MAP (\inst. HD inst.inst_outputs)
         (get_params (HD fn.fn_blocks).bb_instructions))` by simp[MAP_MAP_o, combinTheory.o_DEF] >>
     simp[ALL_DISTINCT_MAP_INJ]) >>
  pairarg_tac >> simp[] >>
  `generated_plan_state_wf_marked spill_base ps''` by
    metis_tac[popmany_plan_wf_marked] >>
  simp[optimistic_swap_plan_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST
    (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))))) ps''.ps_stack` >>
  simp[] >> pairarg_tac >> simp[] >>
  metis_tac[do_swap_wf_marked, stack_get_depth_props]
QED

Theorem native_parameter_residual_budget:
  !fn ch growth spill_base lbl_ctr pending.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    residual_budget_wf spill_base pending
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >> strip_tac >>
  drule_all native_parameter_wf_marked >>
  simp[generated_plan_state_wf_marked_def] >> strip_tac >>
  irule reorderSimTheory.residual_budget_wf_canonical >> simp[]
QED

Theorem native_active_cleanup_resources:
  !S ps liveness cfg fn bb pred_lbl pred_bb inputs layout base ops qs.
    lineage_inventory S ps /\
    generated_plan_state_wf_marked base ps /\
    cfg_preds_of cfg bb.bb_label = [pred_lbl] /\
    1 < LENGTH (cfg_succs_of cfg pred_lbl) /\
    lookup_block pred_lbl fn.fn_blocks = SOME pred_bb /\
    inputs = input_vars_from pred_lbl bb.bb_instructions
      (live_vars_at liveness bb.bb_label 0) /\
    layout = live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions) /\
    set (MAP Var inputs) SUBSET S /\
    S SUBSET set (MAP Var inputs) UNION set (MAP Var layout) UNION FDOM ps.ps_spilled /\
    clean_stack_plan liveness cfg fn bb ps = (ops,qs) ==>
    generated_plan_state_wf_marked base qs /\
    lineage_inventory (set (MAP Var inputs) UNION FDOM ps.ps_spilled) qs /\
    ?m core. lineage_core m core qs /\
      !pending. residual_budget_wf base pending (qs with ps_stack := core)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generated_plan_state_wf_marked bound ps` >>
  `generated_plan_state_wf_marked bound qs` by
    metis_tac[clean_stack_plan_wf_marked] >>
  `lineage_inventory (set (MAP Var inputs) UNION FDOM ps.ps_spilled) qs` by
    (drule_all clean_stack_plan_active_inventory >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `lineage_inventory _ qs` mp_tac >>
  simp[lineage_inventory_def] >> strip_tac >>
  qexistsl_tac [`m`, `core`] >> asm_rewrite_tac[] >> gen_tac >>
  irule reorderSimTheory.residual_budget_wf_canonical >>
  gvs[generated_plan_state_wf_marked_def,
      planSpillBoundsTheory.plan_slots_bounded_def] >>
  metis_tac[]
QED

Theorem analyzed_join_edge_block_spills_empty:
  !fn pred succ pb sb dfg ps ops qs.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block succ fn.fn_blocks = SOME sb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps =
      SOME (ops,qs) ==> qs.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  `sb.bb_label = succ` by metis_tac[lookup_block_label] >>
  `lookup_block sb.bb_label fn.fn_blocks = SOME sb /\
   MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
   LENGTH (cfg_preds_of (cfg_analyze fn) sb.bb_label) <> 1` by simp[] >>
  drule_all join_predecessor_jmp_shape >> strip_tac >>
  drule_all join_predecessor_single_successor >> strip_tac >>
  `inst_wf (LAST pb.bb_instructions)` by
    (`fn_inst_wf fn /\ MEM pb fn.fn_blocks` by
       metis_tac[codegen_ready_fn_def, lookup_block_MEM] >>
     gvs[fn_inst_wf_def] >> first_x_assum irule >>
     qexists_tac `pb` >> simp[LAST_MEM]) >>
  `(LAST pb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  irule phi_jmp_block_spills_empty >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  simp[join_target_ops_def] >>
  `set (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) =
   set (input_vars_from pred sb.bb_instructions
     (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule analyzed_live_out_jmp >> simp[] >> metis_tac[]) >>
  gvs[EXTENSION, MEM_MAP] >> metis_tac[]
QED

Theorem analyzed_active_cleanup_resources:
 !fn pred succ pb sb ps base ops qs.
 codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 cfg_preds_of (cfg_analyze fn) succ = [pred] /\
 1 < LENGTH (cfg_succs_of (cfg_analyze fn) pred) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)))) ps /\
 generated_plan_state_wf_marked base ps /\
 clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn sb ps = (ops,qs)
 ==>
 generated_plan_state_wf_marked base qs /\
 lineage_inventory
   (set (MAP Var (input_vars_from pred sb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))) UNION FDOM ps.ps_spilled) qs /\
 ?m core. lineage_core m core qs /\
   !pending. residual_budget_wf base pending (qs with ps_stack := core)
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `sb.bb_label = succ` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
 drule_all analyzed_live_out_edge_subset >> disch_tac >>
 irule native_active_cleanup_resources >> simp[] >>
 goal_assum (drule_at (Pat `clean_stack_plan _ _ _ _ _ = _`)) >> simp[] >>
 goal_assum (drule_at Any) >>
 gvs[SUBSET_DEF, MEM_MAP] >> metis_tac[]
QED
