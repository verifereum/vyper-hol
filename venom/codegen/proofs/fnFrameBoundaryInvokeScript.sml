(*
 * Helpers for fnFrameBoundary$gen_invoke_frame_sim: the INVOKE step
 * against frameRel$fn_frame_inv, given the callee's function simulation.
 *
 * Notes from the statement check (intuition only; read or ignore):
 * - Label arguments: unit_shape_ok gives fn_shape_ok fn, whose
 *   label_positions_ok forbids Label operands among INVOKE's arguments
 *   (unitShapeDefs), so compute_operands inst = arg_ops.
 * - Callee arity: fmp_lowered_context_wf gives invoke_layout_wf;
 *   invoke_input_arity_ok with canonical_param_prefix (callLayoutDefs)
 *   gives LENGTH args + 1 = LENGTH (get_params entry block) when the
 *   callee has a RETPC_PARAM.
 * - INVOKE arguments and outputs are never return-PC variables
 *   (opaque_use_ok / retpc_use_ok; retpc_shape_ok), so the frame view
 *   reads them as the plain state does.
 * - The caller's spill slots lie in its own region r (spill_alloc_layout_wf,
 *   allocMono's fixed spill base / growing next offset); ordered_spill_regions
 *   makes two MEM regions sharing a byte the same region, so a caller slot
 *   in the callee's closure means fcg_path nm fn.fn_name, a reachable cycle
 *   with the edge fn -> nm (fcgPostorder's reachable_fcg_acyclic lemmas).
 * - The asm semantics has no stack limit and JUMP only looks up o2pc.
 * - INVOKE can have several outputs, so the dead-output popmany postfix
 *   needs a general lemma (regularPostfixSim's structural lemma covers at
 *   most one output).
 * - fnBoundaryProps is downstream of fnFrameBoundary (via venomToAsmProps),
 *   so its small boundary lemmas can't be imported here.
 *)

Theory fnFrameBoundaryInvoke
Ancestors
  fnFrameBoundaryGenRet genFrameSim frameRel contextCodegenRel codegenRel
  regularPostfixSim preparedPrefixSim asmFrame prefixSim stackOpSim
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR frameViewFacts finite_map
  callLayoutDefs fmpWfDefs list rich_list reorderSim planWf stackModel
  regularMemorySim fcgPostorder contextPlanLayoutProps fmpLowerProps

Theorem invoke_source_ok:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?callee args cvs ret rvs.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs /\
    run_blocks fuel ctx callee cvs = IntRet ret rvs /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs'
Proof
  simp[Once step_inst_def, decode_invoke_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_source_halt:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?callee args cvs.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs /\
    run_blocks fuel ctx callee cvs = Halt vs'
Proof
  simp[Once step_inst_def, decode_invoke_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_source_abort:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?callee args cvs.
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops vs = SOME args /\
    setup_callee callee args vs = SOME cvs /\
    run_blocks fuel ctx callee cvs = Abort a vs'
Proof
  simp[Once step_inst_def, decode_invoke_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem invoke_plan_decompose:
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) ==>
  ?iops prepared rops arranged consumed pushed ret_lbl called pops popped
   opts swapped.
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    consumed = arranged with ps_stack :=
      stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack /\
    pushed = FOLDL (\s out.
      s with ps_stack := stack_push (Var out) s.ps_stack)
      consumed inst.inst_outputs /\
    fresh_label "return_label" pushed = (ret_lbl, called) /\
    (if inst.inst_outputs = [] then ([], called)
     else if ~halting \/ LENGTH inst.inst_outputs > 1 then
       popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) called
     else ([], called)) = (pops, popped) /\
    (if inst.inst_outputs = [] \/
        FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([], popped)
     else optimistic_swap_plan dfg inst nl term popped) = (opts, swapped) /\
    final = release_dead_spills nl swapped /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++
      pops ++ opts
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
      generate_regular_inst_plan_def, is_commutative_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  gvs[generate_emit_ops_def, venom_to_evm_name_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `inst.inst_outputs = []`
  >- (gvs[] >> metis_tac[]) >>
  gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  metis_tac[]
QED

Theorem invoke_closure_subset:
  !ctx cp caller callee b.
  fn_directly_calls ctx caller callee /\
  closure_spill_byte ctx cp callee b ==>
  closure_spill_byte ctx cp caller b
Proof
  rw[closure_spill_byte_def, fcg_path_def] >>
  qexists `r` >> simp[] >>
  metis_tac[relationTheory.RTC_RULES, relationTheory.RTC_TRANSITIVE,
            relationTheory.transitive_def]
QED

Theorem invoke_ordered_regions_overlap:
  !rs r s b.
    ordered_spill_regions rs /\ MEM r rs /\ MEM s rs /\
    r.sr_spill_base <= b /\ b < r.sr_spill_end /\
    s.sr_spill_base <= b /\ b < s.sr_spill_end ==> r = s
Proof
  Induct >> simp[ordered_spill_regions_def, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
    arithmeticTheory.NOT_LESS]
QED

Theorem invoke_caller_region_outside_callee:
  !ctx cp caller callee r b.
    ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
    r.sr_fn_name = caller /\ r.sr_spill_base <= b /\ b < r.sr_spill_end /\
    fn_directly_calls ctx caller callee /\
    ~TC (fn_directly_calls ctx) caller caller ==>
    ~closure_spill_byte ctx cp callee b
Proof
  rpt strip_tac >> gvs[closure_spill_byte_def] >>
  rename1 `fcg_path ctx callee other.sr_fn_name` >>
  `r = other` by metis_tac[invoke_ordered_regions_overlap] >>
  gvs[fcg_path_def] >>
  qpat_x_assum `~TC _ _ _` mp_tac >>
  simp[Once relationTheory.TC_CASES1] >>
  metis_tac[relationTheory.RTC_CASES_TC]
QED

Theorem invoke_return_preserves_caller_spills:
  !ctx cp caller callee r off vs cas ras.
    ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
    r.sr_fn_name = caller /\ r.sr_spill_base <= off /\
    off + 32 <= r.sr_spill_end /\
    fn_directly_calls ctx caller callee.fn_name /\
    ~TC (fn_directly_calls ctx) caller caller /\
    fn_return_state_rel ctx cp callee vs cas ras ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off ras.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off cas.as_memory))
Proof
  rpt strip_tac >> irule spill_window_byte_frame >> rpt strip_tac >>
  rename1 `fn_return_state_rel ctx plan callee vs cas ras` >>
  `r.sr_spill_base <= i /\ i < r.sr_spill_end` by decide_tac >>
  `~closure_spill_byte ctx plan callee.fn_name i` by
    metis_tac[invoke_caller_region_outside_callee] >>
  gvs[fn_return_state_rel_def] >> first_x_assum irule >>
  simp[context_spill_byte_def] >> qexists `r` >> simp[] >> decide_tac
QED

Theorem invoke_lowered_targets_wf:
  fmp_lowered_context_wf ctx ==> wf_invoke_targets ctx
Proof
  rw[fmp_lowered_context_wf_def, wf_invoke_targets_def] >>
  first_x_assum drule_all >>
  simp[invoke_layout_wf_def] >> strip_tac >>
  metis_tac[lookup_function_mem, ctx_fn_names_def]
QED

Theorem invoke_context_no_cycle:
  !Inv ctx cp name.
    codegen_context_obligations Inv ctx cp /\
    MEM name (fcg_analyze ctx).fcg_reachable ==>
    ~TC (fn_directly_calls ctx) name name
Proof
  rpt gen_tac >> strip_tac >>
  irule reachable_fcg_acyclic_no_reachable_cycle >>
  gvs[codegen_context_obligations_def, reachable_call_graph_acyclic_def,
      fcg_is_reachable_def] >>
  `wf_invoke_targets ctx` by metis_tac[invoke_lowered_targets_wf] >>
  gvs[ctx_wf_def, ctx_has_entry_def] >> metis_tac[]
QED

Theorem invoke_direct_call:
  ctx_wf ctx /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops ==>
  fn_directly_calls ctx fn.fn_name nm
Proof
  strip_tac >>
  `lookup_function fn.fn_name ctx.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  simp[fn_directly_calls_def] >> metis_tac[]
QED

Theorem invoke_generated_return_spills:
  !Inv ctx cp fn inst nm arg_ops callee r off vs cas ras.
    codegen_context_obligations Inv ctx cp /\
    MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\ callee.fn_name = nm /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end /\
    fn_return_state_rel ctx cp callee vs cas ras ==>
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off ras.as_memory)) =
    word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off cas.as_memory))
Proof
  rpt gen_tac >> strip_tac >>
  `~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name` by
    metis_tac[invoke_context_no_cycle] >>
  irule invoke_return_preserves_caller_spills >>
  gvs[codegen_context_obligations_def, context_plan_layout_wf_def] >>
  metis_tac[invoke_direct_call]
QED
