(* Pure instruction-piece applicability and plan decomposition boundaries.
   Runtime emission subjects can use these without importing symInstPieces. *)
Theory symInstPiecesFacts
Ancestors
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst
  symInstPhiOwn symInstAssignOwn

Theorem singleton_cleanup_ops_bounded:
  popmany_plan [v] ps = (ops,qs) /\ plan_slots_bounded sb ps ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset ops
Proof
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- (`popmany_plan [v] ps = ([],ps)` by
        (irule fnBlockPlanStaticFactsTheory.popmany_plan_absent >> simp[]) >>
      gvs[] >> simp[]) >>
  metis_tac[popmany_singleton_ops_spill_bounded]
QED

Theorem optimistic_swap_ops_bounded:
  optimistic_swap_plan dfg inst nl term ps = (ops,qs) /\ plan_slots_bounded sb ps ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset ops
Proof
  strip_tac >> drule optimistic_swap_result_cases >> strip_tac
  >- (gvs[] >> simp[]) >>
  metis_tac[planSpillBoundsTheory.do_swap_slots_bounded]
QED

Theorem assign_postfix_ops_bounded:
  plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\ qs = release_dead_spills nl ps9 ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (pops ++ opts)
Proof
  strip_tac >>
  Cases_on `MEM x nl`
  >- (gvs[popmany_plan_def] >> drule_all optimistic_swap_ops_bounded >>
      simp[allocMonoTheory.release_dead_spills_next_offset]) >>
  gvs[] >> Cases_on `halt` >> gvs[] >>
  drule_all singleton_cleanup_ops_bounded >>
  simp[allocMonoTheory.release_dead_spills_next_offset]
QED

Theorem regular_postfix_ops_spill_bounded:
  LENGTH inst.inst_outputs <= 1 /\
  plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if inst.inst_outputs = [] \/ halt then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
    = (pops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (pops ++ opts)
Proof
  strip_tac >> Cases_on `inst.inst_outputs`
  >- gvs[planSpillBoundsTheory.ops_spill_bounded_def] >>
  rename1 `inst.inst_outputs = x::xs` >> Cases_on `xs` >> gvs[] >>
  irule assign_postfix_ops_bounded >> qexistsl [`dfg`, `halt`, `inst`, `nl`, `ps7`, `ps8`, `ps9`, `term`, `x`] >>
  Cases_on `MEM x nl` >> gvs[]
QED

Theorem sym_regular_postfix_applicability:
  LENGTH inst.inst_outputs <= 1 /\ generated_plan_state_wf_marked sb ps7 /\
  (if inst.inst_outputs = [] \/ halt then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
    = (pops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  ps7.ps_alloc.sa_spill_base = qs.ps_alloc.sa_spill_base /\
  ps7.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b)
Proof
  strip_tac >>
  `plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  `((if inst.inst_outputs = [] \/ halt then (pops,ps8) = ([],ps7)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7 = (pops,ps8)) /\
    (if inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []
     then (opts,ps9) = ([],ps8)
     else optimistic_swap_plan dfg inst nl term ps8 = (opts,ps9)))` by
    (Cases_on `inst.inst_outputs = []` >>
     gvs[COND_EXPAND, AllCaseEqs()]) >>
  drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> strip_tac >>
  `r.sr_spill_base <= sb` by
    gvs[planSpillBoundsTheory.plan_slots_bounded_def,
      planSpillBoundsTheory.alloc_slots_bounded_def] >>
  drule_all regular_postfix_ops_spill_bounded >> strip_tac >>
  metis_tac[symPostfixSimTheory.scratch_ops_region_confined]
QED

Theorem sym_regular_prefix_applicability:
  generated_plan_state_wf_marked sb ps /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  emitted = arranged with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) arranged.ps_stack) inst.inst_outputs /\
  (if inst.inst_outputs = [] \/ halt then ([],emitted)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted)
    = (pops,popped) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,tail) /\
  qs = release_dead_spills nl tail /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded sb ps /\ residual_budget_wf_marked sb [] ps /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end
Proof
  strip_tac >>
  `residual_budget_wf_marked sb [] ps` by
    metis_tac[deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  drule_all deepResidualSimTheory.selected_input_arranged_marked >> strip_tac >>
  `((if inst.inst_outputs = [] \/ halt then (pops,popped) = ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted = (pops,popped)) /\
    (if inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []
     then (opts,tail) = ([],popped)
     else optimistic_swap_plan dfg inst nl term popped = (opts,tail)))` by
    (Cases_on `inst.inst_outputs = []` >> gvs[COND_EXPAND, AllCaseEqs()]) >>
  drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> strip_tac >>
  gvs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
    deepResidualBudgetTheory.plan_state_residual_wf_marked_def,
    planSpillBoundsTheory.plan_slots_bounded_def,
    planSpillBoundsTheory.alloc_slots_bounded_def] >> gvs[]
QED

Theorem prepared_suffix_concrete_height:
  venom_asm_rel lo ps vs cs /\ ps.ps_stack = residual ++ selected ==>
  LENGTH selected <= LENGTH cs.as_stack
Proof
  simp[codegenRelTheory.venom_asm_rel_def, codegenRelTheory.plan_stack_rel_def] >>
  rpt strip_tac >>
  qpat_x_assum `ps.ps_stack = _ ++ _`
    (mp_tac o AP_TERM ``LENGTH:operand list -> num``) >>
  simp[NoAsms, listTheory.LENGTH_APPEND] >> decide_tac
QED

Theorem asm_unique_label_index:
  !p i lbl. asm_labels_unique p /\ i < LENGTH p /\ EL i p = AsmLabel lbl ==>
    INDEX_OF (AsmLabel lbl) p = SOME i
Proof
  Induct_on `p` >> simp[asmWfTheory.asm_labels_unique_def] >>
  rpt gen_tac >> Cases_on `i` >> simp[] >>
  Cases_on `h` >> gvs[asmWfTheory.asm_labels_unique_def,
    asmSpliceTheory.INDEX_OF_CONS] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  Cases_on `lbl = s` >> gvs[listTheory.MEM_FILTER, listTheory.MEM_MAP] >>
  first_x_assum (qspec_then `EL n p` mp_tac) >> simp[listTheory.EL_MEM]
QED

Theorem asm_static_block_label_index:
  asm_static_wf p /\ asm_block_at p pc code /\
  i < LENGTH code /\ EL i code = AsmLabel lbl ==>
  INDEX_OF (AsmLabel lbl) p = SOME (pc + i)
Proof
  strip_tac >> irule asm_unique_label_index >>
  gvs[asmSymSemTheory.asm_static_wf_def, asmSemTheory.asm_block_at_def]
QED

Theorem sym_bump_postfix_applicability:
  inst.inst_outputs = [ptr;next] /\ ptr <> next /\
  ps7.ps_stack = residual ++ [Var ptr;Var next] /\
  generated_plan_state_wf_marked sb ps7 /\
  (if inst.inst_outputs = [] \/ halt then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
    = (pops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  ps7.ps_alloc.sa_spill_base = qs.ps_alloc.sa_spill_base /\
  ps7.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b)
Proof
  strip_tac >>
  `plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  drule_all bump_popmany_prefix >>
  disch_then (qspecl_then [`ARB`, `ARB`] strip_assume_tac) >>
  `plan_slots_bounded sb ps8` by
    (gvs[planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
  `((if inst.inst_outputs = [] \/ halt then (pops,ps8) = ([],ps7)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7 = (pops,ps8)) /\
    (if inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []
     then (opts,ps9) = ([],ps8)
     else optimistic_swap_plan dfg inst nl term ps8 = (opts,ps9)))` by
    (Cases_on `halt` >>
     Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> fs[] >> gvs[]) >>
  drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> strip_tac >>
  `r.sr_spill_base <= sb` by
    gvs[planSpillBoundsTheory.plan_slots_bounded_def, planSpillBoundsTheory.alloc_slots_bounded_def] >>
  `ops_spill_bounded sb qs.ps_alloc.sa_next_offset opts` by
    (Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []`
     >- gvs[planSpillBoundsTheory.ops_spill_bounded_def] >>
     `optimistic_swap_plan dfg inst nl term ps8 = (opts,ps9)` by gvs[] >>
     drule_all optimistic_swap_ops_bounded >>
     simp[allocMonoTheory.release_dead_spills_next_offset]) >>
  simp[] >> metis_tac[scratch_ops_region_confined]
QED

Theorem istore_plan_decompose:
  inst.inst_opcode = ISTORE /\ inst_wf inst /\
  inst.inst_operands = [dst; value] /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) ==>
  inst.inst_outputs = [] /\ compute_operands inst = [dst; value] /\
  ?iops prepared rops arranged.
    emit_input_plan ISTORE [dst; value] nl ps = (iops,prepared) /\
    reorder_plan dfg [dst; value] prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "SWAP1"; SOEmit "MSTORE"] /\
    qs = release_dead_spills nl (arranged with ps_stack := stack_pop 2 arranged.ps_stack)
Proof
  strip_tac >>
  `inst.inst_outputs = []` by gvs[venomWfTheory.inst_wf_def] >>
  `compute_operands inst = [dst; value]` by
    simp[compute_operands_def, venomInstTheory.python_stack_operands_def, venomInstTheory.ir_specific_operand_order_def] >>
  simp[] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, generate_regular_inst_plan_def,
    is_pre_codegen_opcode_def, venomEffectsTheory.is_commutative_def, venomInstTheory.is_param_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem initial_fmp_plan_decompose:
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_operands = [] /\
  inst.inst_outputs = [x] /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) ==>
  ?pops ps8 opts ps9.
    (if halt then ([],ps with ps_stack := stack_push (Var x) ps.ps_stack)
     else popmany_plan (if MEM x nl then [] else [Var x])
       (ps with ps_stack := stack_push (Var x) ps.ps_stack)) = (pops,ps8) /\
    (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8)) = (opts,ps9) /\
    ops = [SOInitialFmp] ++ (pops ++ opts) /\ qs = release_dead_spills nl ps9
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, venomInstTheory.is_param_opcode_def, generate_regular_inst_plan_def,
    compute_operands_def, venomInstTheory.python_stack_operands_def, venomInstTheory.ir_specific_operand_order_def,
    venomEffectsTheory.is_commutative_def, emit_input_plan_def, planWfTheory.reorder_plan_nil, generate_emit_ops_def,
    stack_pop_def] >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on `MEM x nl` >>
  Cases_on `halt` >> gvs[popmany_plan_def] >> metis_tac[]
QED
