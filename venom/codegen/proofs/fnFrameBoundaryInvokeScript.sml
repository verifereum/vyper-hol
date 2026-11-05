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
