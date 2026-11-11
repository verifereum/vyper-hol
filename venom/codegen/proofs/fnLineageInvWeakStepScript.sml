Theory fnLineageInvWeakStep
Ancestors fnLineageInvReplayBoundary fnLineageInvSilentEnvelope
  fnLineageInvJmpEnvelope fnLineageInvBoundary fnPlanLineageDemand fnPlanLineageDemandSupport
  fnPlanLineagePath fnPlanLineageInventory stackPlanGen venomWf list rich_list
  pred_set finite_map

Theorem demand_available_excludes_suffix_outputs:
  !fn bb k v.
    ssa_form fn /\ MEM bb fn.fn_blocks /\ demand_available fn bb k v ==>
    EVERY (\inst. ~MEM v inst.inst_outputs) (DROP k bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >> simp[EVERY_MEM] >>
  qx_gen_tac `inst` >> strip_tac >>
  qpat_x_assum `MEM inst (DROP _ _)` mp_tac >>
  simp[MEM_DROP] >> strip_tac >> gvs[] >>
  rename1 `k + j < LENGTH bb.bb_instructions` >>
  strip_tac >>
  `demand_available fn bb (k+j) v` by
    (irule demand_available_mono >> qexists_tac `k` >> simp[]) >>
  metis_tac[current_output_not_demand_available]
QED

Theorem analyzed_inventory_suffix_outputs_fresh:
  !fn bb k ps.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k <= LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI) (DROP k bb.bb_instructions) /\
    lineage_inventory
      (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))) ps ==>
    EVERY (\inst. EVERY (\v. ~MEM (Var v) ps.ps_stack /\
      Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs)
      (DROP k bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all analyzed_ordinary_suffix_demand >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  drule lineage_inventory_live_membership >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k)` by
    (strip_tac >>
     `demand_available fn bb k v` by metis_tac[EVERY_MEM] >>
     `EVERY (\inst. ~MEM v inst.inst_outputs) (DROP k bb.bb_instructions)` by
       (irule demand_available_excludes_suffix_outputs >> qexists_tac `fn` >> simp[]) >>
     gvs[EVERY_MEM]) >>
  metis_tac[stackPlanGenTheory.dead_stack_marker_def, venomStateTheory.operand_distinct,
            venomStateTheory.operand_11]
QED

Theorem analyzed_regular_weak_envelope:
  !fn bb k dfg cfg term ps ops qs m core base.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode <> PHI /\
    (EL k bb.bb_instructions).inst_opcode <> JMP /\
    (EL k bb.bb_instructions).inst_opcode <> OFFSET /\
    (EL k bb.bb_instructions).inst_opcode <> NOP /\
    ~is_param_opcode (EL k bb.bb_instructions).inst_opcode /\
    lineage_core m core ps /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
      (EL k bb.bb_instructions).inst_outputs /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label ps = SOME (ops,qs)
    ==>
    lineage_inventory (set (MAP Var
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) qs /\
    (?rest. lineage_core m rest qs /\ residual_budget_wf base [] (qs with ps_stack := rest)) /\
    !r. generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label
      (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
      SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack = REPLICATE m dead_stack_marker ++ core` by gvs[lineage_core_def] >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands (EL k bb.bb_instructions))` by
    metis_tac[fnLineageInvSupportTheory.analyzed_compute_operands_no_marker] >>
  `LENGTH (compute_operands (EL k bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >> metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL k bb.bb_instructions).inst_outputs` by
    (irule genBlockSimTheory.codegen_ready_inst_outputs_distinct >>
     qexists_tac `fn` >> simp[venomInstTheory.fn_insts_def,
       unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands (EL k bb.bb_instructions)) \/
    (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) /\
     ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[fnPlanLineageCallersTheory.analyzed_computed_operand_demand] >>
  `EVERY (\v. ~MEM (Var v) (compute_operands (EL k bb.bb_instructions)) /\
    ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled)
    (EL k bb.bb_instructions).inst_outputs` by
    (gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  pure_once_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- (gen_tac >> irule available_inst_bottom_frame >>
    goal_assum (drule_at Any) >> simp[] >>
    qexistsl_tac [`core`, `m`, `base'`] >>
    simp[] >> gvs[MEM_APPEND, MEM_REPLICATE, dead_stack_marker_def] >> metis_tac[]) >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k)) SUBSET
    set (MAP Var (venomInst$operand_vars (compute_operands (EL k bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))` by
    (Cases_on `(EL k bb.bb_instructions).inst_opcode = LOG`
     >- (irule fnLineageInvSupportTheory.analyzed_log_live_upper_support >> simp[]) >>
     irule fnLineageInvSupportTheory.analyzed_nonlog_live_upper_support >> simp[]) >>
  `set core SUBSET set (MAP Var (venomInst$operand_vars (compute_operands (EL k bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))` by metis_tac[SUBSET_TRANS] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
  irule native_regular_stack_live_inventory >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `core` >> simp[] >>
  conj_tac >- gvs[MEM_APPEND, MEM_REPLICATE] >>
  gvs[SUBSET_DEF, MEM_MAP, reorderSimTheory.input_mem_operand_vars,
      passSharedDefsTheory.MEM_operand_vars_eq_Var] >> metis_tac[]
QED

Theorem analyzed_offset_weak_step:
  !fn bb k dfg cfg term ps ops qs m core spillbase.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = OFFSET /\
    lineage_core m core ps /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    EVERY (\inst. EVERY (\v. ~MEM (Var v) ps.ps_stack /\
      Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs) (DROP k bb.bb_instructions) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label ps = SOME (ops,qs)
    ==>
    (?tail. lineage_core m tail qs /\
      residual_budget_wf spillbase [] (qs with ps_stack := tail) /\
      set tail SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    EVERY (\inst. EVERY (\v. ~MEM (Var v) qs.ps_stack /\
      Var v NOTIN FDOM qs.ps_spilled) inst.inst_outputs) (DROP (SUC k) bb.bb_instructions) /\
    !r. generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label
      (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
      SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (EL k bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `?w lab x. (EL k bb.bb_instructions).inst_operands = [Lit w; Label lab] /\
     (EL k bb.bb_instructions).inst_outputs = [x]` by
    (gvs[inst_wf_def] >> Cases_on `(EL k bb.bb_instructions).inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `DROP k bb.bb_instructions = EL k bb.bb_instructions :: DROP (SUC k) bb.bb_instructions` by
    simp[DROP_CONS_EL] >>
  `~MEM (Var x) core /\ Var x NOTIN FDOM ps.ps_spilled` by
    gvs[EVERY_DEF, lineage_core_def] >>
  `generate_offset_plan (EL k bb.bb_instructions) ps = (ops,qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def]) >>
  drule_all analyzed_offset_live_sets >> strip_tac >>
  drule_all offset_weak_envelope >> strip_tac >>
  conj_tac >- (qexists_tac `core ++ [Var x]` >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (`demand_available fn bb (SUC k) x` by
        (irule current_output_demand_available_suc >> simp[]) >>
      `EVERY (\inst. ~MEM x inst.inst_outputs) (DROP (SUC k) bb.bb_instructions)` by
        (irule demand_available_excludes_suffix_outputs >> qexists_tac `fn` >> simp[]) >>
      gvs[EVERY_MEM, lineage_core_def, MEM_APPEND, MEM_REPLICATE, dead_stack_marker_def] >>
      metis_tac[]) >>
  gen_tac >>
  drule_all fnPlanLineageStagesTheory.generate_offset_plan_frame >>
  disch_then (qspec_then `ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack` assume_tac) >>
  gvs[generate_offset_plan_def, generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
    venomInstTheory.is_raw_fmp_opcode_def, stackModelTheory.stack_push_def,
    SNOC_APPEND, APPEND_ASSOC, stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem analyzed_jmp_weak_replay:
  !fn bb k dfg cfg halt term ps ops qs r.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\ (EL k bb.bb_instructions).inst_opcode = JMP /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) halt term bb.bb_label ps = SOME (ops,qs)
    ==>
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) halt term bb.bb_label
      (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
      SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (EL k bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `(EL k bb.bb_instructions).inst_outputs = [] /\
    ?lab. (EL k bb.bb_instructions).inst_operands = [Label lab]` by
    gvs[inst_wf_def, AllCaseEqs()] >>
  `compute_operands (EL k bb.bb_instructions) = []` by
    simp[compute_operands_def, asmIRTheory.get_non_label_operands_def,
         stackPlanTypesTheory.is_label_operand_def] >>
  `!targets. join_target_ops (liveness_analyze fn) fn bb.bb_label
    (EL k bb.bb_instructions) = SOME targets ==>
    ALL_DISTINCT targets /\ EVERY is_var_operand targets /\
    EVERY (\op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) targets` by
    (rpt strip_tac >>
     drule_all fnLineageInvControlTheory.analyzed_jmp_target_footprint >> strip_tac >>
     drule_all analyzed_jmp_target_end_live >> strip_tac >>
     drule_all analyzed_jmp_live_identity >> strip_tac >>
     gvs[EVERY_MEM, EXTENSION, MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
    venomInstTheory.is_raw_fmp_opcode_def, venomInstTheory.is_param_opcode_def] >> strip_tac >>
  drule_all fnLineageInvActualReplayTheory.generate_jmp_plan_bottom_frame >>
  disch_then (qspec_then `r` assume_tac) >> simp[] >>
  qpat_x_assum `join_reached _ _ _ _ _` mp_tac >> asm_rewrite_tac[] >>
  simp[join_reached_def] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (EL k bb.bb_instructions)` >>
  simp[] >> strip_tac >>
  rename1 `stack_pop (LENGTH targets) qs.ps_stack ++ targets = qs.ps_stack` >>
  `LENGTH targets <= LENGTH qs.ps_stack` by
    (qpat_x_assum `stack_pop _ _ ++ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[stackModelTheory.stack_pop_def, LENGTH_TAKE] >> decide_tac) >>
  simp[fnPlanLineageInventoryTheory.stack_pop_bottom_extension, APPEND_ASSOC] >>
  asm_rewrite_tac[]
QED

Theorem analyzed_weak_envelope_step:
  !fn bb k dfg cfg term ps ops qs m core spillbase.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k < LENGTH bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
      (DROP k bb.bb_instructions) /\
    lineage_core m core ps /\ EVERY is_var_operand core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    EVERY (\inst. EVERY (\v. ~MEM (Var v) ps.ps_stack /\
      Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs) (DROP k bb.bb_instructions) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label ps = SOME (ops,qs)
    ==>
    (?n tail. lineage_core n tail qs /\ EVERY is_var_operand tail /\
      residual_budget_wf spillbase [] (qs with ps_stack := tail) /\
      set tail SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    EVERY (\inst. EVERY (\v. ~MEM (Var v) qs.ps_stack /\
      Var v NOTIN FDOM qs.ps_spilled) inst.inst_outputs) (DROP (SUC k) bb.bb_instructions) /\
    ((EL k bb.bb_instructions).inst_opcode <> NOP /\
     (EL k bb.bb_instructions).inst_opcode <> OFFSET ==>
      lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) qs) /\
    !r. generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label
      (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
      SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `DROP k bb.bb_instructions = EL k bb.bb_instructions :: DROP (SUC k) bb.bb_instructions` by
    simp[DROP_CONS_EL] >>
  fs[EVERY_DEF] >>
  Cases_on `(EL k bb.bb_instructions).inst_opcode = NOP`
  >- suspend "nop" >>
  Cases_on `(EL k bb.bb_instructions).inst_opcode = OFFSET`
  >- suspend "offset" >>
  `lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) qs /\
   (?rest. lineage_core m rest qs /\ residual_budget_wf spillbase [] (qs with ps_stack := rest)) /\
   !r. generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label
      (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
      SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)` by
    (Cases_on `(EL k bb.bb_instructions).inst_opcode = JMP`
     >- (drule_all analyzed_jmp_weak_envelope >> strip_tac >> simp[] >>
         conj_tac >- metis_tac[] >> gen_tac >> irule analyzed_jmp_weak_replay >> simp[] >> metis_tac[]) >>
     drule_all analyzed_regular_weak_envelope >> simp[]) >>
  drule_all fnLineageInvOrdinarySuffixTheory.lineage_inventory_canonical_budget >> strip_tac >>
  conj_tac >- (qexistsl_tac [`n`, `tail`] >> simp[] >> ASM_SET_TAC[]) >>
  conj_tac >- metis_tac[lineage_inventory_live_membership] >>
  conj_tac
  >- (irule analyzed_inventory_suffix_outputs_fresh >> simp[] >>
      conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
      qexists_tac `fn` >> simp[]) >>
  simp[]
QED

Resume analyzed_weak_envelope_step[nop]:
  drule_all fnLineageInvOrdinarySuffixTheory.analyzed_nop_live_identity >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
    venomInstTheory.is_raw_fmp_opcode_def] >> strip_tac >> gvs[] >>
  qexistsl_tac [`m`, `core`] >> simp[]
QED

Resume analyzed_weak_envelope_step[offset]:
  `EVERY (\inst. EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
      inst.inst_outputs) (DROP k bb.bb_instructions)` by (asm_rewrite_tac[EVERY_DEF] >> simp[]) >>
  drule_all analyzed_offset_weak_step >> strip_tac >> simp[] >>
  qexistsl_tac [`m`, `tail`] >> simp[] >>
  gvs[EVERY_MEM, SUBSET_DEF, MEM_MAP] >>
  metis_tac[stackPlanTypesTheory.is_var_operand_def]
QED

Finalise analyzed_weak_envelope_step
