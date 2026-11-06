Theory fnLineageInvSupport
Ancestors
  fnLineageInvBoundary fnPlanLineageDemandSupport fnPlanLineagePhiMaps phiBlock fnLineageInvPhi fnPlanLineagePhiClasses cfgNormBase fnPlanLineagePhiActivation venomExecProps rich_list fnPlanLineageEdge fnPlanLineageLiveness planWfMarked fnPlanPrefix fnPlanLineageInventory fnPlanLineageSuffix fnPlanLineageCallers fnPlanLineagePath fnPlanLineageSetup fnPlanLineageDemand livenessProofs cfgAnalysisProps venomWf
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

Theorem analyzed_small_preds_live_out_excludes_outputs:
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  fn_cfg_edge fn pred succ /\
  LENGTH (cfg_preds_of (cfg_analyze fn) succ) <= 1 /\
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) sb.bb_instructions))
Proof
  strip_tac >>
  drule_all live_end_dominating_def >> strip_tac >>
  `~fn_dominates fn succ pred` by
    (irule small_preds_not_dominates_pred >> simp[]) >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  irule dominating_def_excludes_outputs >> metis_tac[]
QED

Theorem analyzed_active_cleanup_outputs_fresh:
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
 EVERY (\v. ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled)
   (FLAT (MAP (\i. i.inst_outputs) sb.bb_instructions))
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `fn_reachable fn pred /\ fn_cfg_edge fn pred succ` by
   metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze,
             codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
 `LENGTH (cfg_preds_of (cfg_analyze fn) succ) <= 1` by simp[] >>
 drule lineage_inventory_spilled_subset >> disch_tac >>
 drule_all analyzed_live_out_edge_subset >> disch_tac >>
 drule_all analyzed_active_cleanup_resources >> strip_tac >>
 drule_at (Pat `lineage_inventory _ qs`) lineage_inventory_stack_subset >> disch_tac >>
 drule_at (Pat `lineage_inventory _ qs`) lineage_inventory_spilled_subset >> disch_tac >>
 simp[EVERY_MEM] >> rpt strip_tac >>
 `~MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
   (strip_tac >> drule_all analyzed_small_preds_live_out_excludes_outputs >> gvs[]) >>
 gvs[SUBSET_DEF, MEM_MAP, dead_stack_marker_def] >>
 metis_tac[venomStateTheory.operand_distinct, venomStateTheory.operand_11]
QED

Theorem analyzed_join_run_incoming_on_stack:
 !fn entry pred pb succ sb dfg ps0 ops ps i v.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 i < LENGTH (collect_phis sb.bb_instructions) /\
 FIND (\(l,w). l = pred)
   (phi_pairs (EL i (collect_phis sb.bb_instructions)).inst_operands) = SOME (pred,v)
 ==> MEM (Var v) ps.ps_stack
Proof
 rpt gen_tac >> strip_tac >>
 drule_all reachable_phi_incoming_activated >> disch_tac >>
 drule_all generate_block_plan_join_edge_suffix >> strip_tac >>
 simp[MEM_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem analyzed_join_run_phi_witness:
 !fn entry pred pb succ sb dfg ps0 ops ps j.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 j < LENGTH (collect_phis sb.bb_instructions) ==>
 ?w. MEM w (FILTER is_var_operand (EL j (collect_phis sb.bb_instructions)).inst_operands) /\
     MEM w ps.ps_stack
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 `fn_cfg_edge fn pred sb.bb_label` by
   metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
 `MEM (EL j (collect_phis sb.bb_instructions)) (collect_phis sb.bb_instructions)` by
   simp[EL_MEM] >>
 drule_all phi_codegen_edge_wf >>
 simp[phi_edge_uses_wf_def] >> strip_tac >>
 `?v. MEM (pred,v) (phi_pairs (EL j (collect_phis sb.bb_instructions)).inst_operands)` by
   metis_tac[pairTheory.PAIR, pairTheory.FST] >>
 `FIND (\p. FST p = pred)
    (phi_pairs (EL j (collect_phis sb.bb_instructions)).inst_operands) = SOME (pred,v)` by
   (drule_all distinct_key_FIND_member >> simp[]) >>
 `FIND (\(l,w). l = pred)
    (phi_pairs (EL j (collect_phis sb.bb_instructions)).inst_operands) = SOME (pred,v)` by
   gvs[pairTheory.LAMBDA_PROD] >>
 qexists_tac `Var v` >> conj_tac
 >- (simp[MEM_FILTER, is_var_operand_def] >> metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
 drule_all analyzed_join_run_incoming_on_stack >> simp[]
QED

Theorem analyzed_join_released_phi_prefix_preservation:
 !fn entry pred pb succ sb dfg ps0 ops s m core spillbase steps.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,s 0) /\
 lineage_core m core (s 0) /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] ((s 0) with ps_stack := core) /\
 MAP FST steps = collect_phis sb.bb_instructions /\
 (!j. j < LENGTH steps ==>
   ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s 0).ps_stack /\
   Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s 0).ps_spilled) /\
 (!j. j < LENGTH steps ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))) ==>
 !k. k <= LENGTH steps ==>
   (!j w. k <= j /\ j < LENGTH steps /\
     MEM w (FILTER is_var_operand (FST (EL j steps)).inst_operands) /\
     MEM w (s 0).ps_stack ==> MEM w (s k).ps_stack) /\
   (!j. k <= j /\ j < LENGTH steps ==>
     ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s k).ps_stack /\
     Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s k).ps_spilled) /\
   (?rest. lineage_core m rest (s k) /\ EVERY is_var_operand rest /\
     residual_budget_wf spillbase [] ((s k) with ps_stack := rest))
Proof
 rpt gen_tac >> strip_tac >>
 `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 `LENGTH steps = LENGTH (collect_phis sb.bb_instructions)` by
   (qpat_x_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
 `!j. j < LENGTH steps ==>
    FST (EL j steps) = EL j (collect_phis sb.bb_instructions)` by
   (rpt strip_tac >> qpat_x_assum `MAP FST steps = _`
      (mp_tac o Q.AP_TERM `EL j`) >> simp[EL_MAP]) >>
 `!j. j < LENGTH steps ==> MEM (FST (EL j steps)) (collect_phis sb.bb_instructions)` by
   (rpt strip_tac >> simp[EL_MEM]) >>
 `!j. j < LENGTH steps ==>
   (FST (EL j steps)).inst_opcode = PHI /\
   LENGTH (FST (EL j steps)).inst_outputs = 1 /\
   phi_well_formed (FST (EL j steps)).inst_operands` by
   metis_tac[phi_codegen_inst_shape] >>
 match_mp_tac released_phi_prefix_preservation >> qexists_tac `core` >> simp[] >>
 conj_tac >- suspend "nonempty" >>
 conj_tac >- suspend "distinct" >>
 conj_tac >- suspend "disjoint" >>
 suspend "incoming"
QED

Resume analyzed_join_released_phi_prefix_preservation[nonempty]:
 simp[EVERY_EL] >> rpt strip_tac >>
 `LENGTH (FST (EL n steps)).inst_outputs = 1` by metis_tac[] >>
 Cases_on `(FST (EL n steps)).inst_outputs` >> gvs[]
QED

Resume analyzed_join_released_phi_prefix_preservation[distinct]:
 `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) sb.bb_instructions))` by
       (irule ssa_form_block_outputs_distinct >> qexists_tac `fn` >>
        gvs[codegen_ready_fn_def]) >>
     `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
        (collect_phis sb.bb_instructions)))` by metis_tac[phi_collect_outputs_distinct] >>
     `EVERY (\step. LENGTH (FST step).inst_outputs = 1) steps` by
       (simp[EVERY_EL] >> metis_tac[]) >>
     `FLAT (MAP (\step. (FST step).inst_outputs) steps) =
        MAP (\step. HD (FST step).inst_outputs) steps` by
       (qpat_x_assum `EVERY (\step. LENGTH _ = 1) steps` mp_tac >>
        qid_spec_tac `steps` >> Induct >> simp[] >> rpt strip_tac >>
        Cases_on `(FST h).inst_outputs` >> gvs[]) >>
     `MAP (\step. (FST step).inst_outputs) steps =
       MAP (\inst. inst.inst_outputs) (collect_phis sb.bb_instructions)` by
       (qpat_x_assum `MAP FST steps = _` (SUBST1_TAC o SYM) >> simp[MAP_MAP_o, combinTheory.o_DEF]) >>
     metis_tac[]
QED

Resume analyzed_join_released_phi_prefix_preservation[disjoint]:
 `phi_uses_disjoint (collect_phis sb.bb_instructions)` by
       metis_tac[ready_block_phi_uses_disjoint] >>
     rpt gen_tac >> strip_tac >> strip_tac >>
     `i < LENGTH steps /\ j < LENGTH steps` by metis_tac[] >>
     `FST (EL i steps) = EL i (collect_phis sb.bb_instructions)` by metis_tac[] >>
     fs[MEM_FILTER] >> Cases_on `x` >> gvs[is_var_operand_def] >>
     `MEM s' (inst_uses (EL i (collect_phis sb.bb_instructions))) /\
      MEM s' (inst_uses (EL j (collect_phis sb.bb_instructions)))` by
       (simp[inst_uses_def, MEM_operand_vars_eq_Var] >> metis_tac[]) >>
     metis_tac[phi_disjoint_use_indices]
QED

Resume analyzed_join_released_phi_prefix_preservation[incoming]:
 rpt strip_tac >> irule analyzed_join_run_phi_witness >> metis_tac[]
QED

Finalise analyzed_join_released_phi_prefix_preservation

Theorem analyzed_phi_output_dead_at_entry:
 !fn entry lbl bb phi v.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn lbl /\ lbl <> entry /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs ==>
 ~MEM v (live_vars_at (liveness_analyze fn) lbl 0)
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
   (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
    metis_tac[fn_reachable_cfg_analyze]) >>
 `?i. i < LENGTH (collect_phis bb.bb_instructions) /\
      EL i (collect_phis bb.bb_instructions) = phi` by metis_tac[MEM_EL] >>
 qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
 `i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = phi` by
   (qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
    simp[EL_APPEND1]) >>
 `!k. k <= i ==> ~MEM v (inst_uses (EL k bb.bb_instructions))` by
   (gen_tac >> disch_tac >> irule reachable_phi_prefix_no_output_use_alias >>
    goal_assum (drule_at Any) >> simp[] >>
    qexistsl_tac [`bb`, `entry`, `fn`, `lbl`] >> simp[] >>
    `k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
    `EL k bb.bb_instructions = EL k (collect_phis bb.bb_instructions)` by
      (qpat_assum `bb.bb_instructions = _` (mp_tac o Q.AP_TERM `\xs. EL k xs`) >>
       simp[EL_APPEND1]) >> metis_tac[EL_MEM]) >>
 `~MEM v (inst_uses phi)` by
   (qpat_x_assum `!k. k <= i ==> _` (qspec_then `i` mp_tac) >> simp[]) >>
 `~MEM v (live_vars_at (liveness_analyze fn) lbl i)` by
   (drule livenessProofsTheory.live_vars_at_transfer >>
    disch_then (qspecl_then [`lbl`, `bb`, `i`] mp_tac) >> simp[] >>
    simp[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
         venomInstTheory.inst_defs_def, MEM_FILTER]) >>
 irule analyzed_dead_before_use_free_interval >>
 goal_assum (drule_at Any) >> simp[] >> qexists_tac `i` >> simp[]
QED

Theorem analyzed_phi_output_excluded_edge_input:
 !fn entry pred lbl bb phi v.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn lbl /\ lbl <> entry /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs ==>
 ~MEM v (input_vars_from pred bb.bb_instructions
   (live_vars_at (liveness_analyze fn) lbl 0))
Proof
 rpt gen_tac >> strip_tac >>
 `~MEM v (live_vars_at (liveness_analyze fn) lbl 0)` by
   (irule analyzed_phi_output_dead_at_entry >> metis_tac[]) >>
 strip_tac >> drule input_vars_from_projected_membership >> strip_tac >>
 `~MEM v (inst_uses phi')` by
   (irule reachable_phi_prefix_no_output_use_alias >> metis_tac[]) >>
 `MEM (Var v) phi'.inst_operands` by metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
 gvs[venomInstTheory.inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]
QED

Theorem analyzed_singleton_live_out_excludes_phi_output:
 !fn entry pred pb succ sb phi v.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 MEM phi (collect_phis sb.bb_instructions) /\ MEM v phi.inst_outputs ==>
 ~MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 drule_all analyzed_live_out_singleton >>
 simp[pred_setTheory.EXTENSION] >> strip_tac >>
 `~MEM v (input_vars_from pred sb.bb_instructions
   (live_vars_at (liveness_analyze fn) succ 0))` by
   (irule analyzed_phi_output_excluded_edge_input >> metis_tac[]) >>
 metis_tac[]
QED

Theorem analyzed_singleton_phi_outputs_fresh:
 !fn entry pred pb succ sb ps.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps ==>
 EVERY (\phi. EVERY (\v. ~MEM (Var v) ps.ps_stack /\
   Var v NOTIN FDOM ps.ps_spilled) phi.inst_outputs)
   (collect_phis sb.bb_instructions)
Proof
 rpt gen_tac >> strip_tac >> simp[EVERY_MEM] >>
 gen_tac >> disch_tac >> gen_tac >> disch_tac >>
 `~MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
   (irule analyzed_singleton_live_out_excludes_phi_output >> metis_tac[]) >>
 drule lineage_inventory_stack_subset >>
 drule lineage_inventory_spilled_subset >>
 simp[pred_setTheory.SUBSET_DEF, MEM_MAP, dead_stack_marker_def] >>
 disch_then (qspec_then `Var v` mp_tac) >> simp[] >>
 disch_tac >> disch_then (qspec_then `Var v` mp_tac) >> simp[]
QED

Theorem analyzed_phi_suffix_live_backward:
 !fn lbl bb k v.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 k <= LENGTH (collect_phis bb.bb_instructions) /\
 ~MEM v (FLAT (MAP (\phi. phi.inst_outputs)
   (DROP k (collect_phis bb.bb_instructions)))) /\
 MEM v (live_vars_at (liveness_analyze fn) lbl
   (LENGTH (collect_phis bb.bb_instructions))) ==>
 MEM v (live_vars_at (liveness_analyze fn) lbl k)
Proof
 rpt gen_tac >> strip_tac >>
 qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
 irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
 goal_assum drule >> simp[] >>
 qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >> simp[] >>
 reverse conj_tac
 >- (qpat_x_assum `bb.bb_instructions = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
 rpt strip_tac >>
 `EL k' bb.bb_instructions = EL k' (collect_phis bb.bb_instructions)` by
   (qpat_assum `bb.bb_instructions = _` (mp_tac o Q.AP_TERM `EL k'`) >>
    simp[EL_APPEND1]) >>
 `MEM (EL k' (collect_phis bb.bb_instructions))
    (DROP k (collect_phis bb.bb_instructions))` by
   (simp[MEM_EL] >> qexists_tac `k' - k` >> simp[EL_DROP]) >>
 qpat_x_assum `~MEM v (FLAT _)` mp_tac >>
 simp[MEM_FLAT, MEM_MAP] >> metis_tac[venomInstTheory.inst_defs_def]
QED

Theorem analyzed_released_phi_schedule_coverage:
 !fn lbl bb steps s n.
 wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 MAP FST steps = collect_phis bb.bb_instructions /\ n = LENGTH steps /\
 (!j. j < n ==> LENGTH (FST (EL j steps)).inst_outputs = 1) /\
 (!j v. j < n /\ MEM v (live_vars_at (liveness_analyze fn) lbl (SUC j)) /\
   (v = HD (FST (EL j steps)).inst_outputs \/
    MEM (Var v) (s j).ps_stack \/ Var v IN FDOM (s j).ps_spilled) ==>
   MEM (Var v) (s (SUC j)).ps_stack \/ Var v IN FDOM (s (SUC j)).ps_spilled) /\
 (!v. MEM v (live_vars_at (liveness_analyze fn) lbl n) /\
   ~MEM v (FLAT (MAP (\phi. phi.inst_outputs) (collect_phis bb.bb_instructions))) ==>
   MEM (Var v) (s 0).ps_stack \/ Var v IN FDOM (s 0).ps_spilled) ==>
 !v. MEM v (live_vars_at (liveness_analyze fn) lbl n) ==>
   MEM (Var v) (s n).ps_stack \/ Var v IN FDOM (s n).ps_spilled
Proof
 rpt gen_tac >> strip_tac >>
 `n = LENGTH (collect_phis bb.bb_instructions)` by
   (qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
 `!j. j < n ==> FST (EL j steps) = EL j (collect_phis bb.bb_instructions)` by
   (rpt strip_tac >> qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `EL j`) >>
    simp[EL_MAP]) >>
 `!k. k <= n ==> !v. MEM v (live_vars_at (liveness_analyze fn) lbl n) /\
   (!j. k <= j /\ j < n ==> ~MEM v (FST (EL j steps)).inst_outputs) ==>
   MEM (Var v) (s k).ps_stack \/ Var v IN FDOM (s k).ps_spilled` suffices_by
   (disch_then (qspec_then `n` mp_tac) >> simp[]) >>
 Induct
 >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
     qpat_x_assum `MEM _ (collect_phis _)` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     metis_tac[]) >>
 rpt strip_tac >>
 `k < n /\ k <= n` by decide_tac >>
 `MEM v (live_vars_at (liveness_analyze fn) lbl (SUC k))` by
   suspend "backward" >>
 first_x_assum irule >> simp[] >>
 Cases_on `v = HD (EL k (collect_phis bb.bb_instructions)).inst_outputs` >> simp[] >>
 first_x_assum irule >> simp[] >> rpt strip_tac >>
 Cases_on `j = k` >- (gvs[] >>
   `LENGTH (EL j (collect_phis bb.bb_instructions)).inst_outputs = 1` by metis_tac[] >>
   Cases_on `(EL j (collect_phis bb.bb_instructions)).inst_outputs` >> gvs[]) >>
 `SUC k <= j` by decide_tac >> metis_tac[]
QED

Resume analyzed_released_phi_schedule_coverage[backward]:
 irule analyzed_phi_suffix_live_backward >> goal_assum drule >> simp[] >>
 reverse conj_tac >- metis_tac[] >>
 strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
 qpat_x_assum `MEM _ (DROP _ _)`
   (qx_choose_then `idx` strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
 `SUC k + idx < LENGTH steps` by (fs[LENGTH_DROP] >> decide_tac) >>
 `EL idx (DROP (SUC k) (collect_phis bb.bb_instructions)) =
    FST (EL (SUC k + idx) steps)` by simp[EL_DROP] >>
 qpat_x_assum `!j. SUC k <= j /\ _ ==> _` (qspec_then `SUC k + idx` mp_tac) >>
 gvs[EL_DROP, arithmeticTheory.ADD_COMM]
QED

Finalise analyzed_released_phi_schedule_coverage

Theorem analyzed_join_released_phi_coverage:
 !fn entry pred pb succ sb dfg ps0 ops s m core spillbase steps n.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,s 0) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) (s 0) /\
 lineage_core m core (s 0) /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] ((s 0) with ps_stack := core) /\
 MAP FST steps = collect_phis sb.bb_instructions /\ n = LENGTH steps /\
 (!j. j < n ==> FST (SND (EL j steps)) =
    live_vars_at (liveness_analyze fn) succ (SUC j)) /\
 (!j. j < n ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))) ==>
 !v. MEM v (live_vars_at (liveness_analyze fn) succ n) ==>
   MEM (Var v) (s n).ps_stack \/ Var v IN FDOM (s n).ps_spilled
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 `MEM succ (cfg_analyze fn).cfg_dfs_pre` by
   (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
    metis_tac[fn_reachable_cfg_analyze]) >>
 `n = LENGTH (collect_phis sb.bb_instructions)` by
   (qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
 `!j. j < n ==> FST (EL j steps) = EL j (collect_phis sb.bb_instructions)` by
   (rpt strip_tac >> qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `EL j`) >>
    simp[EL_MAP]) >>
 `!j. j < LENGTH steps ==>
   ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s 0).ps_stack /\
   Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s 0).ps_spilled` by
   suspend "fresh" >>
 `MEM succ (cfg_succs_of (cfg_analyze fn) pred)` by simp[] >>
 `!j. j < LENGTH steps ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))` by metis_tac[] >>

 gen_tac >> disch_tac >>
 irule (INST_TYPE [alpha |-> ``:string list # bool``]
   analyzed_released_phi_schedule_coverage) >> goal_assum (drule_at Any) >>
 qexistsl_tac [`sb`, `steps`] >> simp[] >>
 conj_tac >- suspend "initial" >>
 conj_tac >- suspend "step" >>
 rpt strip_tac >> irule (cj 2 phi_codegen_inst_shape) >>
 qexistsl_tac [`sb`, `fn`] >> simp[EL_MEM]
QED

Resume analyzed_join_released_phi_coverage[fresh]:
 drule_all analyzed_singleton_phi_outputs_fresh >>
 simp[EVERY_MEM] >> strip_tac >> gen_tac >> disch_tac >>
 `LENGTH (FST (EL j steps)).inst_outputs = 1` by
   (irule (cj 2 phi_codegen_inst_shape) >> qexistsl_tac [`sb`, `fn`] >> simp[EL_MEM]) >>
 `MEM (HD (FST (EL j steps)).inst_outputs) (FST (EL j steps)).inst_outputs` by
   (Cases_on `(FST (EL j steps)).inst_outputs` >> gvs[]) >>
 `MEM (FST (EL j steps)) (collect_phis sb.bb_instructions)` by
   (qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `EL j`) >>
    simp[EL_MAP] >> metis_tac[EL_MEM]) >>
 metis_tac[]
QED

Resume analyzed_join_released_phi_coverage[step]:
 rpt gen_tac >> strip_tac >>
 `j <= LENGTH steps /\ j < LENGTH steps` by decide_tac >>
 drule_all analyzed_join_released_phi_prefix_preservation >> strip_tac >>
 `?w. MEM w (FILTER is_var_operand (FST (EL j steps)).inst_operands) /\
      MEM w (s 0).ps_stack` by
   (drule_all analyzed_join_run_phi_witness >> simp[]) >>
 `MEM w (s j).ps_stack` by
   (qpat_x_assum `!j' w. _` (qspecl_then [`j`, `w`] mp_tac) >> simp[]) >>
 Cases_on `generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
    (SND (SND (EL j steps))) (s j)` >>
 irule released_phi_core_live_coverage >> goal_assum (drule_at Any) >>
 qexistsl_tac [`spillbase`, `rest`, `m`] >> gvs[] >> metis_tac[]
QED

Resume analyzed_join_released_phi_coverage[initial]:
 qx_gen_tac `u` >> strip_tac >>
 `MEM u (live_vars_at (liveness_analyze fn) succ 0)` by
   (irule analyzed_phi_suffix_live_backward >> goal_assum drule >> simp[]) >>
 `MEM u (input_vars_from pred sb.bb_instructions
   (live_vars_at (liveness_analyze fn) succ 0))` by
   (irule livenessProofsTheory.input_vars_from_non_phi >> simp[] >> rpt strip_tac >>
    `MEM u (inst_uses inst)` by
      (simp[inst_uses_def, MEM_operand_vars_eq_Var] >>
       gvs[MEM_MAP] >>
       metis_tac[cfgNormBaseTheory.phi_pairs_mem_var, pairTheory.PAIR]) >>
    drule_all phi_codegen_input_dead_after_prefix >> simp[] >> metis_tac[]) >>
 drule_all analyzed_live_out_singleton >>
 simp[pred_setTheory.EXTENSION] >> strip_tac >>
 `MEM u (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
   metis_tac[] >>
 drule lineage_inventory_live_membership >> metis_tac[]
QED

Finalise analyzed_join_released_phi_coverage

Theorem analyzed_join_initial_phi_support:
 !fn pred pb succ sb ps.
 wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps ==>
 !op. (MEM op ps.ps_stack /\ op <> dead_stack_marker) \/
   op IN FDOM ps.ps_spilled ==>
 ?v. op = Var v /\
   ((MEM v (live_vars_at (liveness_analyze fn) succ 0) /\
     ~MEM v (raw_phi_inputs sb.bb_instructions)) \/
    ?phi. MEM phi (collect_phis sb.bb_instructions) /\
      MEM (pred,v) (phi_pairs phi.inst_operands))
Proof
 rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
 drule lineage_inventory_live_membership >> strip_tac >>
 `?v. op = Var v /\ MEM v (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions))` by metis_tac[] >>
 drule_all analyzed_live_out_singleton >>
 simp[pred_setTheory.EXTENSION] >> strip_tac >>
 `MEM v (input_vars_from pred sb.bb_instructions
   (live_vars_at (liveness_analyze fn) succ 0))` by metis_tac[] >>
 drule input_vars_from_projected_membership >> metis_tac[]
QED

Theorem analyzed_phi_origin_selected_input:
 !fn entry pred succ sb k v.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 k < LENGTH (collect_phis sb.bb_instructions) /\
 MEM (Var v) (FILTER is_var_operand
   (EL k (collect_phis sb.bb_instructions)).inst_operands) /\
 ((MEM v (live_vars_at (liveness_analyze fn) succ 0) /\
    ~MEM v (raw_phi_inputs sb.bb_instructions)) \/
  (?i. k <= i /\ i < LENGTH (collect_phis sb.bb_instructions) /\
    MEM (pred,v) (phi_pairs (EL i (collect_phis sb.bb_instructions)).inst_operands)) \/
  MEM v (FLAT (MAP (\phi. phi.inst_outputs)
    (TAKE k (collect_phis sb.bb_instructions))))) ==>
 MEM (pred,v) (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands)
Proof
 rpt gen_tac >> strip_tac >>
 `MEM sb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM (EL k (collect_phis sb.bb_instructions))
    (collect_phis sb.bb_instructions)` by simp[EL_MEM] >>
 `phi_well_formed (EL k (collect_phis sb.bb_instructions)).inst_operands` by
   metis_tac[phi_codegen_inst_shape] >>
 `MEM v (inst_uses (EL k (collect_phis sb.bb_instructions)))` by
   gvs[MEM_FILTER, inst_uses_def, MEM_operand_vars_eq_Var] >>
 `phi_uses_disjoint (collect_phis sb.bb_instructions)` by
   (metis_tac[ready_block_phi_uses_disjoint])
 >~ [`~MEM v (raw_phi_inputs _)`]
 >- (`?l. MEM (l,v) (phi_pairs
         (EL k (collect_phis sb.bb_instructions)).inst_operands)` by
       (gvs[MEM_FILTER] >> metis_tac[venomWfTheory.phi_well_formed_var_pair]) >>
     `MEM v (raw_phi_inputs sb.bb_instructions)` by
       (simp[NoAsms, raw_phi_inputs_def, MEM_FLAT, MEM_MAP] >>
        qexists_tac `MAP SND (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands)` >>
        conj_tac >- metis_tac[] >> simp[MEM_MAP] >>
        qexists_tac `(l,v)` >> simp[]) >> metis_tac[])
 >- (`MEM v (inst_uses (EL i (collect_phis sb.bb_instructions)))` by
       (simp[inst_uses_def, MEM_operand_vars_eq_Var] >>
        metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
     `i = k` by (irule phi_disjoint_use_indices >> metis_tac[]) >> gvs[]) >>
 gvs[MEM_FLAT, MEM_MAP] >>
 `MEM phi (collect_phis sb.bb_instructions)` by metis_tac[MEM_TAKE] >>
 `~MEM v (inst_uses (EL k (collect_phis sb.bb_instructions)))` by
   (irule reachable_phi_prefix_no_output_use_alias >> metis_tac[]) >> metis_tac[]
QED

Theorem analyzed_join_released_phi_support:
 !fn entry pred pb succ sb dfg ps0 ops s m core spillbase steps n h.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,s 0) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) (s 0) /\
 lineage_core m core (s 0) /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] ((s 0) with ps_stack := core) /\
 MAP FST steps = collect_phis sb.bb_instructions /\ n = LENGTH steps /\
 (!j. j < n ==> FST (SND (EL j steps)) =
    live_vars_at (liveness_analyze fn) succ (SUC j)) /\
 (!j. j < n ==> SND (SND (EL j steps)) = h) /\
 (!j. j < n ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))) ==>
 !op. (MEM op (s n).ps_stack /\ op <> dead_stack_marker) \/
   op IN FDOM (s n).ps_spilled ==>
 ?v. op = Var v /\
   (MEM v (live_vars_at (liveness_analyze fn) succ n) \/
    (h /\ MEM v (FLAT (MAP (\phi. phi.inst_outputs) (collect_phis sb.bb_instructions)))))
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 `MEM succ (cfg_analyze fn).cfg_dfs_pre` by
   (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
    metis_tac[fn_reachable_cfg_analyze]) >>
 `n = LENGTH (collect_phis sb.bb_instructions)` by
   (qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
 `!j. j < n ==> FST (EL j steps) = EL j (collect_phis sb.bb_instructions)` by
   (rpt strip_tac >> qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `EL j`) >> simp[EL_MAP]) >>
 `!k. k <= n ==> !op.
    (MEM op (s k).ps_stack /\ op <> dead_stack_marker) \/ op IN FDOM (s k).ps_spilled ==>
    ?v. op = Var v /\
     ((MEM v (live_vars_at (liveness_analyze fn) succ k) /\
       MEM v (live_vars_at (liveness_analyze fn) succ 0) /\
       ~MEM v (raw_phi_inputs sb.bb_instructions)) \/
      (?i. k <= i /\ i < n /\
        MEM (pred,v) (phi_pairs (EL i (collect_phis sb.bb_instructions)).inst_operands)) \/
      (MEM v (FLAT (MAP (\phi. phi.inst_outputs) (TAKE k (collect_phis sb.bb_instructions)))) /\
       (h \/ MEM v (live_vars_at (liveness_analyze fn) succ k))))` suffices_by
   (disch_then (qspec_then `n` mp_tac) >>
    simp[] >> disch_tac >> gen_tac >> disch_tac >>
    first_x_assum drule >> strip_tac >> qexists_tac `v` >> simp[] >>
    metis_tac[arithmeticTheory.NOT_LESS_EQUAL]) >>
 Induct
 >- (simp[] >> rpt strip_tac >>
     `?v. op = Var v /\
        ((MEM v (live_vars_at (liveness_analyze fn) succ 0) /\
          ~MEM v (raw_phi_inputs sb.bb_instructions)) \/
         ?phi. MEM phi (collect_phis sb.bb_instructions) /\
           MEM (pred,v) (phi_pairs phi.inst_operands))` by
       (irule analyzed_join_initial_phi_support >> metis_tac[]) >>
     qexists_tac `v` >> simp[] >> gvs[MEM_EL] >> metis_tac[]) >>
 rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >>
 `k < n /\ k <= n` by decide_tac >>
 suspend "step"
QED

Resume analyzed_join_released_phi_support[step]:
 `MEM succ (cfg_succs_of (cfg_analyze fn) pred)` by simp[] >>
 `!j. j < LENGTH steps ==>
   ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s 0).ps_stack /\
   Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s 0).ps_spilled` by
   (drule_all analyzed_singleton_phi_outputs_fresh >> simp[EVERY_MEM] >>
    strip_tac >> gen_tac >> disch_tac >>
    `MEM (FST (EL j steps)) (collect_phis sb.bb_instructions)` by
      (qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `EL j`) >>
       simp[EL_MAP] >> metis_tac[EL_MEM]) >>
    `LENGTH (FST (EL j steps)).inst_outputs = 1` by metis_tac[phi_codegen_inst_shape] >>
    `MEM (HD (FST (EL j steps)).inst_outputs) (FST (EL j steps)).inst_outputs` by
      (Cases_on `(FST (EL j steps)).inst_outputs` >> gvs[]) >> metis_tac[]) >>
 `k <= LENGTH steps` by decide_tac >>
 `!j. j < LENGTH steps ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))` by metis_tac[] >>
 drule_all analyzed_join_released_phi_prefix_preservation >> strip_tac >>
 `MEM (FST (EL k steps)) (collect_phis sb.bb_instructions)` by simp[EL_MEM] >>
 `k < LENGTH (collect_phis sb.bb_instructions)` by decide_tac >>
 `?w. MEM w (FILTER is_var_operand (FST (EL k steps)).inst_operands) /\
    MEM w (s 0).ps_stack` by
   (drule_all analyzed_join_run_phi_witness >> simp[]) >>
 `MEM w (s k).ps_stack` by
   (qpat_x_assum `!j w. _` (qspecl_then [`k`, `w`] mp_tac) >> simp[]) >>
 `~MEM (Var (HD (FST (EL k steps)).inst_outputs)) (s k).ps_stack /\
  Var (HD (FST (EL k steps)).inst_outputs) NOTIN FDOM (s k).ps_spilled` by
   (qpat_x_assum `!j. k <= j /\ _ ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
 `?d. stack_get_phi_depth (FILTER is_var_operand (FST (EL k steps)).inst_operands)
     (s k).ps_stack = SOME d` by
   (Cases_on `stack_get_phi_depth (FILTER is_var_operand (FST (EL k steps)).inst_operands)
       (s k).ps_stack` >> simp[] >>
    fs[stack_get_phi_depth_def, stack_find_NONE_EVERY, EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
 `d < LENGTH (s k).ps_stack /\ stack_peek d (s k).ps_stack <> dead_stack_marker` by
   metis_tac[genBlockSimTheory.stack_get_phi_depth_var_not_marker] >>
 `MEM (stack_peek d (s k).ps_stack) (s k).ps_stack` by
   (simp[stack_peek_def] >> irule EL_MEM >> decide_tac) >>
 `is_var_operand (stack_peek d (s k).ps_stack) /\
  MEM (stack_peek d (s k).ps_stack) rest` by
   (gvs[lineage_core_def] >> fs[MEM_APPEND, MEM_REPLICATE, EVERY_MEM] >> metis_tac[]) >>
 `LENGTH (FILTER (\op. op = stack_peek d (s k).ps_stack) (s k).ps_stack) = 1` by
   suspend "count" >>
 `?x. stack_peek d (s k).ps_stack = Var x` by
   (Cases_on `stack_peek d (s k).ps_stack` >> gvs[is_var_operand_def]) >>
 `MEM (Var x) (FILTER is_var_operand (FST (EL k steps)).inst_operands)` by
   suspend "selected" >>
 `MEM (pred,x) (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands)` by
   suspend "origin" >>
 Cases_on `generate_phi_plan (FST (EL k steps)) (FST (SND (EL k steps)))
   (SND (SND (EL k steps))) (s k)` >>
 `is_var_operand (Var x)` by simp[is_var_operand_def] >>
 `LENGTH (FILTER (\z. z = Var x) (s k).ps_stack) = 1` by metis_tac[] >>
 `s (SUC k) = release_dead_spills (FST (SND (EL k steps))) r` by
   (qpat_assum `!j. j < n ==> s (SUC j) = _` (qspec_then `k` mp_tac) >> simp[]) >>
 drule_all released_phi_inventory_delta >>
 disch_then (qspec_then `op` mp_tac) >>
 suspend "semantic"
QED

Resume analyzed_join_released_phi_support[count]:
 `LIST_ELEM_COUNT (stack_peek d (s k).ps_stack) rest <= 1` by
   (fs[reorderSimTheory.residual_budget_wf_def, LIST_ELEM_COUNT_THM] >> metis_tac[]) >>
 `0 < LIST_ELEM_COUNT (stack_peek d (s k).ps_stack) rest` by
   (drule (iffRL LIST_ELEM_COUNT_MEM) >> decide_tac) >>
 `FILTER (\z. z = stack_peek d (s k).ps_stack) (REPLICATE m dead_stack_marker) = []` by
   (simp[FILTER_EQ_NIL, EVERY_MEM, MEM_REPLICATE] >> metis_tac[]) >>
 gvs[lineage_core_def] >> fs[FILTER_APPEND, LIST_ELEM_COUNT_DEF] >> decide_tac
QED

Resume analyzed_join_released_phi_support[selected]:
 qpat_x_assum `stack_get_phi_depth _ _ = SOME d` mp_tac >>
 rewrite_tac[stack_get_phi_depth_def] >>
 disch_then (mp_tac o MATCH_MP genBlockSimTheory.stack_find_el) >>
 `PRE (LENGTH (s k).ps_stack - d) = LENGTH (s k).ps_stack - 1 - d` by decide_tac >>
 simp[EL_REVERSE] >> fs[stack_peek_def]
QED

Resume analyzed_join_released_phi_support[origin]:
 irule analyzed_phi_origin_selected_input >>
 goal_assum (drule_at Any) >> simp[] >>
 qpat_x_assum `k <= n ==> _` mp_tac >> simp[] >>
 disch_then (qspec_then `Var x` mp_tac) >> simp[] >> metis_tac[]
QED

Resume analyzed_join_released_phi_support[semantic]:
 `phi_block_ready (liveness_analyze fn) sb` by metis_tac[phi_codegen_block_ready] >>
 `MEM x (inst_uses (EL k (collect_phis sb.bb_instructions)))` by
   (simp[inst_uses_def, MEM_operand_vars_eq_Var] >>
    metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
 `~MEM x (live_vars_at (liveness_analyze fn) succ (SUC k))` by
   (irule analyzed_phi_incoming_dead_after >> goal_assum (drule_at Any) >>
    simp[] >> qexists_tac `k` >> simp[]) >>
 `FST (SND (EL k steps)) = live_vars_at (liveness_analyze fn) succ (SUC k) /\
  SND (SND (EL k steps)) = h /\
  FST (EL k steps) = EL k (collect_phis sb.bb_instructions)` by metis_tac[] >>
 simp[operand_to_string_def] >> disch_tac >>
 `SUC k <= LENGTH sb.bb_instructions /\
  EL k sb.bb_instructions = EL k (collect_phis sb.bb_instructions)` by
   (qspec_then `sb.bb_instructions` strip_assume_tac collect_phis_prefix >>
    conj_tac
    >- (qpat_assum `sb.bb_instructions = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
    qpat_assum `sb.bb_instructions = _` (mp_tac o Q.AP_TERM `EL k`) >> simp[EL_APPEND1]) >>
 `live_vars_at (liveness_analyze fn) succ k =
  liveness_transfer fn.fn_blocks (EL k (collect_phis sb.bb_instructions))
   (live_vars_at (liveness_analyze fn) succ (SUC k))` by
   (drule livenessProofsTheory.live_vars_at_transfer >>
    disch_then (qspecl_then [`succ`, `sb`, `k`] mp_tac) >> simp[]) >>
 Cases_on `op = Var (HD (EL k (collect_phis sb.bb_instructions)).inst_outputs)`
 >- suspend "new_output" >>
 qpat_x_assum `k <= n ==> _` mp_tac >> simp[] >>
 disch_then (qspec_then `op` mp_tac) >>
 (impl_tac >- metis_tac[]) >>
 strip_tac >> qexists_tac `v` >> simp[]
 >~ [`~MEM v (raw_phi_inputs _)`] >- suspend "live_origin"
 >~ [`MEM (pred,v) (phi_pairs _)`] >- suspend "pending_origin"
 >~ [`MEM v (FLAT _) /\ (_ \/ MEM v (live_vars_at _ _ _))`]
 >- suspend "processed_live"
 >> suspend "processed_h"
QED

Resume analyzed_join_released_phi_support[new_output]:
 `TAKE (SUC k) (collect_phis sb.bb_instructions) =
  TAKE k (collect_phis sb.bb_instructions) ++ [EL k (collect_phis sb.bb_instructions)]` by
   (qspec_then `collect_phis sb.bb_instructions` (qspec_then `k` mp_tac) TAKE_EL_SNOC >>
    simp[SNOC_APPEND, arithmeticTheory.ADD1]) >>
 `MEM (HD (EL k (collect_phis sb.bb_instructions)).inst_outputs)
   (EL k (collect_phis sb.bb_instructions)).inst_outputs` by
   ( `LENGTH (EL k (collect_phis sb.bb_instructions)).inst_outputs = 1` by
       metis_tac[phi_codegen_inst_shape] >>
     Cases_on `(EL k (collect_phis sb.bb_instructions)).inst_outputs` >> gvs[]) >>
 gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Resume analyzed_join_released_phi_support[live_origin]:
 `~MEM v (inst_uses (EL k (collect_phis sb.bb_instructions)))` by
   (strip_tac >>
    `phi_well_formed (EL k (collect_phis sb.bb_instructions)).inst_operands` by
      metis_tac[phi_codegen_inst_shape] >>
    `?l. MEM (l,v) (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands)` by
      (fs[inst_uses_def, phi_well_formed_uses_pairs, MEM_MAP] >> metis_tac[pairTheory.PAIR, pairTheory.SND]) >>
    qpat_x_assum `~MEM v (raw_phi_inputs _)` mp_tac >>
    simp[raw_phi_inputs_def, MEM_FLAT, MEM_MAP] >>
    qexists_tac `MAP SND (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands)` >>
    conj_tac >- metis_tac[EL_MEM] >>
    simp[MEM_MAP] >> qexists_tac `(l,v)` >> simp[]) >>
 disj1_tac >>
 fs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
    MEM_FILTER, livenessDefsTheory.MEM_ordered_inst_uses]
QED

Resume analyzed_join_released_phi_support[pending_origin]:
 Cases_on `i = k`
 >- (`phi_edge_uses_wf fn sb (EL k (collect_phis sb.bb_instructions))` by
       metis_tac[phi_codegen_edge_wf, EL_MEM] >>
     `ALL_DISTINCT (MAP FST (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands))` by
       fs[phi_edge_uses_wf_def] >>
     `FIND (\p. FST p = pred) (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands) = SOME (pred,x)` by
       (drule_all distinct_key_FIND_member >> simp[]) >>
     `FIND (\p. FST p = pred) (phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands) = SOME (pred,v)` by
       (qspec_then `FST` (qspecl_then
         [`phi_pairs (EL k (collect_phis sb.bb_instructions)).inst_operands`, `(pred,v)`] mp_tac)
         distinct_key_FIND_member >> simp[] >> metis_tac[]) >>
     `v = x` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
     fs[MEM_MAP] >> metis_tac[]) >>
 disj2_tac >> disj1_tac >> qexists_tac `i` >> simp[] >> decide_tac
QED

Resume analyzed_join_released_phi_support[processed_h]:
 qspec_then `collect_phis sb.bb_instructions` (qspec_then `k` mp_tac) TAKE_EL_SNOC >>
 simp[SNOC_APPEND, arithmeticTheory.ADD1] >> disch_then SUBST1_TAC >>
 simp[MAP_APPEND, FLAT_APPEND, MEM_APPEND]
QED

Resume analyzed_join_released_phi_support[processed_live]:
 `?phi. MEM phi (TAKE k (collect_phis sb.bb_instructions)) /\ MEM v phi.inst_outputs` by
   (fs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
 `MEM phi (collect_phis sb.bb_instructions)` by metis_tac[MEM_TAKE] >>
 `~MEM v (inst_uses (EL k (collect_phis sb.bb_instructions)))` by
   (irule reachable_phi_prefix_no_output_use_alias >> metis_tac[EL_MEM]) >>
 `MEM v (live_vars_at (liveness_analyze fn) succ (SUC k))` by
   (fs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
       MEM_FILTER, livenessDefsTheory.MEM_ordered_inst_uses]) >>
 qspec_then `collect_phis sb.bb_instructions` (qspec_then `k` mp_tac) TAKE_EL_SNOC >>
 simp[SNOC_APPEND, arithmeticTheory.ADD1] >> disch_then SUBST1_TAC >>
 simp[MAP_APPEND, FLAT_APPEND, MEM_APPEND]
QED

Finalise analyzed_join_released_phi_support


Theorem analyzed_join_released_phi_inventory:
 !fn entry pred pb succ sb dfg ps0 ops s m core spillbase steps n.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,s 0) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) (s 0) /\
 lineage_core m core (s 0) /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] ((s 0) with ps_stack := core) /\
 MAP FST steps = collect_phis sb.bb_instructions /\ n = LENGTH steps /\
 (!j. j < n ==> FST (SND (EL j steps)) =
    live_vars_at (liveness_analyze fn) succ (SUC j)) /\
 (!j. j < n ==> SND (SND (EL j steps)) = F) /\
 (!j. j < n ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))) ==>
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) succ n))) (s n) /\
 ?rest. lineage_core m rest (s n) /\ EVERY is_var_operand rest /\
   residual_budget_wf spillbase [] ((s n) with ps_stack := rest)
Proof
 rpt gen_tac >> strip_tac >>
 `!op. (MEM op (s n).ps_stack /\ op <> dead_stack_marker) \/
    op IN FDOM (s n).ps_spilled ==>
    ?v. op = Var v /\ MEM v (live_vars_at (liveness_analyze fn) succ n)` by
   (mp_tac (Q.INST [`h` |-> `F`] (SPEC_ALL analyzed_join_released_phi_support)) >>
    (impl_tac >- metis_tac[]) >> simp[]) >>
 `!v. MEM v (live_vars_at (liveness_analyze fn) succ n) ==>
    MEM (Var v) (s n).ps_stack \/ Var v IN FDOM (s n).ps_spilled` by
   (mp_tac (SPEC_ALL analyzed_join_released_phi_coverage) >>
    (impl_tac >- metis_tac[]) >> simp[]) >>
 `MEM sb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 `MEM succ (cfg_succs_of (cfg_analyze fn) pred)` by simp[] >>
 `!j. j < LENGTH steps ==>
   ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s 0).ps_stack /\
   Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s 0).ps_spilled` by
   (drule_all analyzed_singleton_phi_outputs_fresh >> simp[EVERY_MEM] >>
    strip_tac >> gen_tac >> disch_tac >>
    `MEM (FST (EL j steps)) (collect_phis sb.bb_instructions)` by
      (qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `EL j`) >>
       simp[EL_MAP] >> disch_tac >> irule EL_MEM >>
       qpat_assum `MAP FST steps = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
    `LENGTH (FST (EL j steps)).inst_outputs = 1` by metis_tac[phi_codegen_inst_shape] >>
    `MEM (HD (FST (EL j steps)).inst_outputs) (FST (EL j steps)).inst_outputs` by
      (Cases_on `(FST (EL j steps)).inst_outputs` >> gvs[]) >> metis_tac[]) >>
 `!j. j < LENGTH steps ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))` by metis_tac[] >>
 mp_tac (SPEC_ALL analyzed_join_released_phi_prefix_preservation) >>
 (impl_tac >- metis_tac[]) >>
 disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
 drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
 simp[lineage_inventory_def] >> qexistsl [`m`, `rest`] >> simp[] >>
 qpat_x_assum `n = LENGTH steps` SUBST_ALL_TAC >>
 qpat_x_assum `lineage_core m rest _` mp_tac >>
 simp[lineage_core_def] >> disch_tac >>
 qpat_x_assum `EVERY is_var_operand rest` mp_tac >>
 qpat_x_assum `!op. _ ==> ?v. op = Var v /\ _` mp_tac >>
 qpat_x_assum `!v. MEM v (live_vars_at _ _ _) ==> _` mp_tac >>
 qpat_x_assum `(s (LENGTH steps)).ps_stack = _` mp_tac >>
 POP_ASSUM_LIST (K all_tac) >>
 simp[EVERY_MEM, EXTENSION, IN_UNION, MEM_MAP] >>
 rpt gen_tac >> rpt disch_tac >>
 `!e. MEM e rest ==> e <> dead_stack_marker` by
   (rpt strip_tac >> gvs[dead_stack_marker_def] >>
    qpat_x_assum `!e. MEM e rest ==> _` drule >>
    simp[stackPlanTypesTheory.is_var_operand_def]) >>
 qpat_x_assum `(s (LENGTH steps)).ps_stack = _` kall_tac >>
 fs[dead_stack_marker_def] >>
 conj_tac
 >- (gen_tac >> eq_tac
     >- (strip_tac >> qpat_x_assum `!op. _ ==> ?v. _` irule >> simp[] >>
         strip_tac >> gvs[])
     >> strip_tac >> gvs[] >> first_x_assum irule >> simp[]) >>
 gen_tac >> disch_tac >>
 qpat_x_assum `!op. _ ==> ?v. _` (qspec_then `op` mp_tac) >>
 simp[] >> strip_tac >> gvs[stackPlanTypesTheory.is_var_operand_def]
QED

Theorem analyzed_join_initial_spill_support:
 !fn entry pred pb succ sb dfg ps0 ops ps m core spillbase.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps /\
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) ==>
 !op. op IN FDOM ps.ps_spilled ==> ?v. op = Var v /\
   MEM v (live_vars_at (liveness_analyze fn) succ 0) /\
   ~MEM v (raw_phi_inputs sb.bb_instructions) /\
   ~MEM v (FLAT (MAP (\phi. phi.inst_outputs) (collect_phis sb.bb_instructions)))
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
   metis_tac[lookup_block_MEM, lookup_block_label] >>
 `MEM succ (cfg_succs_of (cfg_analyze fn) pred)` by simp[] >>
 `fn_cfg_edge fn pred sb.bb_label` by
   metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze] >>
 drule_all analyzed_singleton_phi_outputs_fresh >> simp[EVERY_MEM] >> disch_tac >>
 drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
 gen_tac >> disch_tac >>
 mp_tac (SPEC_ALL analyzed_join_initial_phi_support) >>
 (impl_tac >- simp[]) >> disch_then (qspec_then `op` mp_tac) >> simp[] >>
 strip_tac >> gvs[] >>
 `~MEM v (FLAT (MAP (\phi. phi.inst_outputs) (collect_phis sb.bb_instructions)))` by
   (simp[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
 reverse (Cases_on `MEM v (live_vars_at (liveness_analyze fn) sb.bb_label 0) /\
   ~MEM v (raw_phi_inputs sb.bb_instructions)`)
 >- (gvs[] >>
     drule_all phi_codegen_edge_wf >> disch_tac >> fs[phi_edge_uses_wf_def] >>
     `FIND (\p. FST p = pred) (phi_pairs phi.inst_operands) = SOME (pred,v)` by
       (drule_all distinct_key_FIND_member >> simp[]) >>
     `FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) = SOME (pred,v)` by
       gvs[pairTheory.LAMBDA_PROD] >>
     `?i. i < LENGTH (collect_phis sb.bb_instructions) /\
       phi = EL i (collect_phis sb.bb_instructions)` by metis_tac[MEM_EL] >>
     qpat_x_assum `phi = EL i _` SUBST_ALL_TAC >>
     `MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pred)` by simp[] >>
     `MEM (Var v) ps.ps_stack` by
       (drule_all analyzed_join_run_incoming_on_stack >> simp[]) >>
     gvs[lineage_core_def, MEM_APPEND, MEM_REPLICATE, dead_stack_marker_def,
         DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
 gvs[]
QED

Theorem analyzed_phi_live_through_prefix:
 !fn lbl bb v j.
 codegen_ready_fn fn /\ fn_reachable fn lbl /\
 lookup_block lbl fn.fn_blocks = SOME bb /\
 MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
 ~MEM v (raw_phi_inputs bb.bb_instructions) /\
 ~MEM v (FLAT (MAP (\phi. phi.inst_outputs) (collect_phis bb.bb_instructions))) /\
 j <= LENGTH (collect_phis bb.bb_instructions) ==>
 MEM v (live_vars_at (liveness_analyze fn) lbl j)
Proof
 rpt gen_tac >> strip_tac >>
 `wf_function fn` by gvs[codegen_ready_fn_def] >>
 `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
   metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
 `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
 qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
 `!k. k < j ==> EL k bb.bb_instructions = EL k (collect_phis bb.bb_instructions)` by
   (rpt strip_tac >> qpat_assum `bb.bb_instructions = _` (mp_tac o Q.AP_TERM `EL k`) >>
    simp[EL_APPEND1]) >>
 `j <= LENGTH bb.bb_instructions` by
   (qpat_assum `bb.bb_instructions = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
 qpat_x_assum `bb.bb_instructions = _` kall_tac >>
 `!k. k < j ==> ~MEM v (inst_defs (EL k bb.bb_instructions))` by
   (rpt strip_tac >> qpat_assum `!k. k < j ==> EL k _ = _` drule >> disch_then SUBST1_TAC >>
    `MEM (EL k (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
      (irule EL_MEM >> decide_tac) >>
    fs[MEM_FLAT, MEM_MAP, inst_defs_def] >> metis_tac[]) >>
 mp_tac (SRULE [LET_THM] livenessProofsTheory.live_vars_at_forward_or_used) >>
 disch_then (qspecl_then [`fn`, `lbl`, `bb`, `0`, `j`, `v`] mp_tac) >>
 simp[] >> strip_tac >> simp[] >>
 `EL k bb.bb_instructions = EL k (collect_phis bb.bb_instructions)` by simp[] >>
 fs[] >>
 `MEM (EL k (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
   (irule EL_MEM >> decide_tac) >>
 `phi_well_formed (EL k (collect_phis bb.bb_instructions)).inst_operands` by
   metis_tac[phi_codegen_inst_shape] >>
 `?l. MEM (l,v) (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands)` by
   (fs[inst_uses_def, phi_well_formed_uses_pairs, MEM_MAP] >> metis_tac[pairTheory.PAIR, pairTheory.SND]) >>
 `MEM v (raw_phi_inputs bb.bb_instructions)` by
   (simp[NoAsms, raw_phi_inputs_def, MEM_FLAT, MEM_MAP] >>
    qexists_tac `MAP SND (phi_pairs (EL k (collect_phis bb.bb_instructions)).inst_operands)` >>
    conj_tac >- metis_tac[] >> simp[MEM_MAP] >> qexists_tac `(l,v)` >> simp[]) >>
 gvs[]
QED

Theorem analyzed_join_initial_spills_live:
 !fn entry pred pb succ sb dfg ps0 ops ps m core spillbase j.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps /\
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) /\
 j <= LENGTH (collect_phis sb.bb_instructions) ==>
 !op. op IN FDOM ps.ps_spilled ==> ?v. op = Var v /\
   MEM v (live_vars_at (liveness_analyze fn) succ j)
Proof
 rpt gen_tac >> strip_tac >>
 mp_tac (SPEC_ALL analyzed_join_initial_spill_support) >>
 (impl_tac >- simp[]) >> disch_tac >> gen_tac >> disch_tac >>
 first_x_assum drule >> strip_tac >> gvs[] >>
 irule analyzed_phi_live_through_prefix >> metis_tac[]
QED

Theorem analyzed_join_phi_release_identity:
 !fn entry pred pb succ sb dfg ps0 ops ps m core spillbase j qs.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps /\
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) /\
 j <= LENGTH (collect_phis sb.bb_instructions) /\ qs.ps_spilled = ps.ps_spilled ==>
 release_dead_spills (live_vars_at (liveness_analyze fn) succ j) qs = qs
Proof
 rpt gen_tac >> strip_tac >>
 irule fnPlanLineageReplayTheory.release_dead_spills_live_domain >> simp[] >>
 mp_tac (SPEC_ALL analyzed_join_initial_spills_live) >>
 (impl_tac >- simp[]) >> simp[]
QED

Theorem actual_phi_prefix_trace:
 !k insts lv dfg cfg fn lbl halt np bl i ps ops qs.
 k <= LENGTH insts /\ EVERY (\inst. inst.inst_opcode = PHI) (TAKE k insts) /\
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts ps = SOME (ops,qs) ==>
 ?s. s 0 = ps /\ s k = qs /\
   (!j. j < k ==> s (SUC j) = SND (generate_phi_plan (EL j insts)
     (if DROP (SUC j) insts = [] then live_vars_at lv lbl bl
      else live_vars_at lv lbl (i+j+np+1)) halt (s j))) /\
   (!j. j <= k ==> (s j).ps_spilled = ps.ps_spilled)
Proof
 Induct_on `k`
 >- (simp[generate_block_insts_prefix_def] >> rpt gen_tac >>
     qexists_tac `\j. ps` >> simp[]) >>
 Cases_on `insts` >- simp[] >> rpt gen_tac >> strip_tac >>
 gvs[generate_block_insts_prefix_def, generate_inst_plan_def,
     is_pre_codegen_opcode_def, is_unlowered_fmp_opcode_def,
     is_unlowered_internal_call_opcode_def, is_raw_fmp_opcode_def,
     AllCaseEqs()] >>
 first_x_assum drule_all >> strip_tac >>
 drule phi_plan_spilled_unchanged >> disch_tac >>
 qexists_tac `\j. if j = 0 then ps else s (PRE j)` >> simp[] >>
 conj_tac
 >- (gen_tac >> Cases_on `j`
     >- (gvs[] >> Cases_on `t` >> gvs[]) >>
     simp[EL, arithmeticTheory.ADD_CLAUSES, GSYM arithmeticTheory.ADD1] >>
     rpt strip_tac >> qpat_x_assum `!j. j < k ==> _` drule >>
     simp[arithmeticTheory.ADD_CLAUSES, GSYM arithmeticTheory.ADD1]) >>
 gen_tac >> Cases_on `j` >> simp[]
QED

Theorem analyzed_join_raw_phi_trace_release:
 !fn entry pred pb succ sb dfg ps0 ops ps m core spillbase s k halt.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps /\
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) /\
 k <= LENGTH (collect_phis sb.bb_instructions) /\ s 0 = ps /\
 (!j. j < k ==> s (SUC j) = SND (generate_phi_plan
   (EL j (collect_phis sb.bb_instructions))
   (live_vars_at (liveness_analyze fn) succ (SUC j)) halt (s j))) ==>
 !j. j < k ==> s (SUC j) = release_dead_spills
   (live_vars_at (liveness_analyze fn) succ (SUC j))
   (SND (generate_phi_plan (EL j (collect_phis sb.bb_instructions))
     (live_vars_at (liveness_analyze fn) succ (SUC j)) halt (s j)))
Proof
 rpt gen_tac >> strip_tac >>
 `!j. j <= k ==> (s j).ps_spilled = ps.ps_spilled` by
   (Induct >- simp[] >> strip_tac >>
    `s (SUC j) = SND (generate_phi_plan
      (EL j (collect_phis sb.bb_instructions))
      (live_vars_at (liveness_analyze fn) succ (SUC j)) halt (s j))` by simp[] >>
    Cases_on `generate_phi_plan (EL j (collect_phis sb.bb_instructions))
      (live_vars_at (liveness_analyze fn) succ (SUC j)) halt (s j)` >>
    drule phi_plan_spilled_unchanged >> gvs[]) >>
 gen_tac >> disch_tac >>
 `SUC j <= LENGTH (collect_phis sb.bb_instructions)` by decide_tac >>
 `release_dead_spills (live_vars_at (liveness_analyze fn) succ (SUC j))
   (s (SUC j)) = s (SUC j)` by
   (irule analyzed_join_phi_release_identity >> goal_assum drule >> simp[] >>
    metis_tac[]) >>
 metis_tac[]
QED

Theorem analyzed_join_actual_phi_prefix_schedule:
 !fn entry pred pb succ sb dfg ps0 ops ps m core spillbase insts k bl halt pops qs.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,ps) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn)
   pred (LENGTH pb.bb_instructions)))) ps /\
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) /\
 k = LENGTH (collect_phis sb.bb_instructions) /\ k <= LENGTH insts /\
 TAKE k insts = collect_phis sb.bb_instructions /\
 (k < LENGTH insts \/ bl = k) /\
 generate_block_insts_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ
   halt 0 bl 0 k insts ps = SOME (pops,qs) ==>
 ?s steps. s 0 = ps /\ s k = qs /\
 MAP FST steps = collect_phis sb.bb_instructions /\ k = LENGTH steps /\
 (!j. j < k ==> FST (SND (EL j steps)) =
    live_vars_at (liveness_analyze fn) succ (SUC j)) /\
 (!j. j < k ==> SND (SND (EL j steps)) = halt) /\
 (!j. j < k ==> s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
   (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
     (SND (SND (EL j steps))) (s j))))
Proof
 rpt gen_tac >> strip_tac >>
 `EVERY (\inst. inst.inst_opcode = PHI) (TAKE k insts)` by
   (simp[EVERY_MEM] >> metis_tac[collect_phis_mem]) >>
 drule_all actual_phi_prefix_trace >> strip_tac >>
 `!j. j < k ==> s (SUC j) = SND (generate_phi_plan
   (EL j (collect_phis sb.bb_instructions))
   (live_vars_at (liveness_analyze fn) succ (SUC j)) halt (s j))` by
   (gen_tac >> disch_tac >>
    qpat_x_assum `!j. j < k ==> _` drule >>
    `EL j (collect_phis sb.bb_instructions) = EL j insts` by
      (qpat_x_assum `TAKE k insts = _` (mp_tac o Q.AP_TERM `EL j`) >> simp[EL_TAKE]) >>
    Cases_on `DROP (SUC j) insts = []` >> simp[GSYM arithmeticTheory.ADD1] >>
    `SUC j = k /\ bl = k` by
      (fs[DROP_EQ_NIL] >> decide_tac) >> simp[]) >>
 `!j. j < k ==> s (SUC j) = release_dead_spills
   (live_vars_at (liveness_analyze fn) succ (SUC j))
   (SND (generate_phi_plan (EL j (collect_phis sb.bb_instructions))
     (live_vars_at (liveness_analyze fn) succ (SUC j)) halt (s j)))` by
   (mp_tac (SPEC_ALL analyzed_join_raw_phi_trace_release) >>
    (impl_tac >- simp[]) >> simp[]) >>
 qexists_tac `s` >>
 qexists_tac `GENLIST (\j. (EL j (collect_phis sb.bb_instructions),
   live_vars_at (liveness_analyze fn) succ (SUC j), halt)) k` >>
 simp[EL_GENLIST, MAP_GENLIST, combinTheory.o_DEF] >>
 irule GENLIST_EL >> simp[]
QED
