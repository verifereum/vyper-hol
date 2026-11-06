Theory fnLineageInvOffset
Ancestors fnLineageInvPointLive reorderSim fnPlanLineageStages fnPlanLineageInventory stackPlanGen stackModel stackPlanTypes venomState list pred_set

Theorem offset_lineage_inventory_iff:
  !inst w lab x before after ps ops qs.
    inst.inst_operands = [Lit w; Label lab] /\ inst.inst_outputs = [x] /\
    set before = set (FILTER (\v. v <> x) after) /\
    lineage_inventory (set (MAP Var before)) ps /\
    generate_offset_plan inst ps = (ops,qs) ==>
    (lineage_inventory (set (MAP Var after)) qs <=> MEM x after)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all generate_offset_plan_frame >> strip_tac >> gvs[] >>
  eq_tac
  >- (strip_tac >> drule lineage_inventory_stack_subset >>
      simp[SUBSET_DEF, MEM_APPEND, MEM_MAP, dead_stack_marker_def] >>
      metis_tac[operand_distinct, operand_11]) >>
  strip_tac >>
  qpat_x_assum `lineage_inventory _ ps` mp_tac >>
  simp[lineage_inventory_def] >> strip_tac >>
  `~MEM (Var x) core /\ Var x NOTIN FDOM ps.ps_spilled` by
    (qpat_x_assum `set core UNION _ = _` mp_tac >>
     simp[EXTENSION, MEM_MAP] >>
     disch_then (qspec_then `Var x` mp_tac) >>
     simp[] >> gvs[EXTENSION, MEM_FILTER]) >>
  qexistsl_tac [`m`, `core ++ [Var x]`] >>
  simp[lineage_core_def, APPEND_ASSOC, ALL_DISTINCT_APPEND,
       EVERY_APPEND, is_var_operand_def, DISJOINT_UNION] >>
  conj_tac >- gvs[lineage_core_def] >>
  gvs[EXTENSION, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem offset_lineage_inventory_budget:
  !inst w lab x before after ps ops qs base.
    inst.inst_operands = [Lit w; Label lab] /\ inst.inst_outputs = [x] /\
    set before = set (FILTER (\v. v <> x) after) /\
    lineage_inventory (set (MAP Var before)) ps /\
    generate_offset_plan inst ps = (ops,qs) /\ MEM x after /\
    (?m core. lineage_core m core ps /\
      residual_budget_wf base [] (ps with ps_stack := core)) ==>
    ?n tail. lineage_core n tail qs /\
      residual_budget_wf base [] (qs with ps_stack := tail)
Proof
  rpt gen_tac >> strip_tac >>
  `lineage_inventory (set (MAP Var after)) qs` by
    (drule_all offset_lineage_inventory_iff >> simp[]) >>
  drule_all generate_offset_plan_frame >> strip_tac >> gvs[] >>
  qpat_x_assum `lineage_inventory _ (_ with ps_stack := _)` mp_tac >>
  simp[lineage_inventory_def] >> strip_tac >>
  qexistsl_tac [`m'`, `core'`] >> simp[] >>
  irule reorderSimTheory.residual_budget_wf_canonical >>
  gvs[reorderSimTheory.residual_budget_wf_def]
QED

Theorem analyzed_offset_inventory:
  !fn bb j w lab x ps ops qs base.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    j < LENGTH bb.bb_instructions /\
    (EL j bb.bb_instructions).inst_opcode = OFFSET /\
    (EL j bb.bb_instructions).inst_operands = [Lit w; Label lab] /\
    (EL j bb.bb_instructions).inst_outputs = [x] /\
    lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label j))) ps /\
    generate_offset_plan (EL j bb.bb_instructions) ps = (ops,qs) /\
    (?m core. lineage_core m core ps /\
      residual_budget_wf base [] (ps with ps_stack := core)) ==>
    lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC j)))) qs /\
    (?n tail. lineage_core n tail qs /\
      residual_budget_wf base [] (qs with ps_stack := tail))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM x (live_vars_at (liveness_analyze fn) bb.bb_label (SUC j))` by
    (rewrite_tac[arithmeticTheory.ADD1] >>
     irule analyzed_offset_output_live_after >> simp[] >> metis_tac[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[EXTENSION] >> metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze]) >>
  `set (live_vars_at (liveness_analyze fn) bb.bb_label j) =
   set (FILTER (\v. v <> x) (live_vars_at (liveness_analyze fn) bb.bb_label (SUC j)))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `j`] mp_tac) >>
     simp[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
       venomInstTheory.inst_uses_def, venomInstTheory.inst_defs_def,
       livenessDefsTheory.ordered_inst_uses_def, venomInstTheory.python_stack_operands_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
       venomInstTheory.ir_specific_operand_order_def]) >>
  conj_tac
  >- (drule_all offset_lineage_inventory_iff >> simp[]) >>
  irule offset_lineage_inventory_budget >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
