Theory fnLineageInvSupport
Ancestors
  fnPlanLineageCallers fnPlanLineagePath fnPlanLineageSetup livenessProofs cfgAnalysisProps venomWf
  stackPlanGen asmIR venomInst passSharedDefs codegenReadyCompute unitShapeDefs list pred_set

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

Theorem analyzed_ordinary_live_inventory:
  !fn bb i dfg cfg term lbl ps m core base ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands (EL i bb.bb_instructions)) /\
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
