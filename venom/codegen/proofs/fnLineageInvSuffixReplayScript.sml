Theory fnLineageInvSuffixReplay
Ancestors fnLineageInvActualReplay fnLineageInvOrdinarySuffix fnLineageInvBoundary
  fnLineageInvSupport fnPlanLineageCallers fnPlanLineagePath
  fnPlanLineageStages fnPlanLineageInventory reorderSim stackPlanGen
  venomWf venomInst list rich_list pred_set

Theorem analyzed_ordinary_inst_bottom_frame:
 !fn bb k dfg cfg term base ps ops qs m.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 k < LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI) (DROP k bb.bb_instructions) /\
 (EL k bb.bb_instructions).inst_opcode <> JMP /\
 ~is_param_opcode (EL k bb.bb_instructions).inst_opcode /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))) ps /\
 (?n core. lineage_core n core ps /\ residual_budget_wf base [] (ps with ps_stack := core)) /\
 generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
   (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label ps = SOME (ops,qs)
 ==>
 generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
   (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label
   (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 SOME (ops, qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 `(EL k bb.bb_instructions).inst_opcode <> PHI` by
   (gvs[EVERY_MEM] >> first_x_assum irule >> simp[MEM_DROP, MEM_EL] >> qexists_tac `0` >> simp[]) >>
 Cases_on `(EL k bb.bb_instructions).inst_opcode = NOP`
 >- (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
 Cases_on `(EL k bb.bb_instructions).inst_opcode = OFFSET`
 >- suspend "offset" >>
 drule_all lineage_inventory_canonical_budget >> strip_tac >>
 `ps.ps_stack = REPLICATE n' dead_stack_marker ++ tail` by gvs[lineage_core_def] >>
 `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
   (drule lineage_inventory_live_membership >> simp[]) >>
 `!v. MEM (Var v) (compute_operands (EL k bb.bb_instructions)) ==>
    MEM (Var v) tail \/ Var v IN FDOM ps.ps_spilled` by
   (rpt strip_tac >>
    `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k)` by
      (irule analyzed_computed_operand_demand >> simp[]) >>
    gvs[MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
 `!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
    demand_available fn bb k v` by
   (rpt strip_tac >> irule analyzed_suffix_inventory_demand >>
    simp[] >> qexistsl_tac [`tail`, `n'`, `ps`] >>
    asm_rewrite_tac[] >>
    qpat_x_assum `set tail UNION _ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
 `ssa_form fn` by gvs[codegen_ready_fn_def] >>
 drule_all definition_support_output_fresh >> strip_tac >>
 `EVERY (\v. ~MEM (Var v) (compute_operands (EL k bb.bb_instructions)) /\
     ~MEM (Var v) tail /\ Var v NOTIN FDOM ps.ps_spilled)
     (EL k bb.bb_instructions).inst_outputs` by
   (gvs[EVERY_MEM, MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
 `MEM (EL k bb.bb_instructions) (fn_insts fn)` by
   (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
 `ALL_DISTINCT (EL k bb.bb_instructions).inst_outputs` by
   metis_tac[codegen_ready_inst_outputs_distinct] >>
 `LENGTH (compute_operands (EL k bb.bb_instructions)) <= 16` by
   (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >> metis_tac[EL_MEM]) >>
 `EVERY (\x. x <> dead_stack_marker) (compute_operands (EL k bb.bb_instructions))` by
   metis_tac[analyzed_compute_operands_no_marker] >>
 suspend "regular"
QED

Resume analyzed_ordinary_inst_bottom_frame[regular]:
 qabbrev_tac `canon = ps with ps_stack := tail` >>
 Cases_on `generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
   (EL k bb.bb_instructions) (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
   F term bb.bb_label canon` >>
 rename1 `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ canon = (cops,cqs)` >>
 `!r. generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
   (EL k bb.bb_instructions) (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
   F term bb.bb_label (canon with ps_stack := REPLICATE r dead_stack_marker ++ canon.ps_stack) =
   (cops,cqs with ps_stack := REPLICATE r dead_stack_marker ++ cqs.ps_stack)` by
   (gen_tac >> irule generate_regular_plan_bottom_frame >>
    simp[Abbr `canon`] >> metis_tac[]) >>
 `canon with ps_stack := REPLICATE n' dead_stack_marker ++ canon.ps_stack = ps` by
   (simp[Abbr `canon`, stackPlanTypesTheory.plan_state_component_equality]) >>
 first_assum (qspec_then `n'` assume_tac) >>
 first_assum (qspec_then `m+n'` assume_tac) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 gvs[Abbr `canon`, GSYM REPLICATE_APPEND, APPEND_ASSOC]
QED

Resume analyzed_ordinary_inst_bottom_frame[offset]:
 `inst_wf (EL k bb.bb_instructions)` by
   (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
 qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >> strip_tac >>
 `?x. (EL k bb.bb_instructions).inst_outputs = [x]` by
   (qpat_x_assum `LENGTH _ = 1` mp_tac >> simp[LENGTH_EQ_NUM_compute]) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 drule_all generate_offset_plan_frame >> strip_tac >>
 gvs[APPEND_ASSOC]
QED

Finalise analyzed_ordinary_inst_bottom_frame
