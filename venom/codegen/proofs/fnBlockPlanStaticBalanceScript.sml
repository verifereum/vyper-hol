Theory fnBlockPlanStaticBalance
Ancestors
  stackPlanGen stackPlanTypes stackModel asmIR integer

(* Physical planner bookkeeping; SOEmit is deliberately opaque. *)
Definition stack_op_weight_def:
  (stack_op_weight (SOPush op) = (1:int)) /\
  (stack_op_weight (SOPop n) = -(&n)) /\
  (stack_op_weight (SOSwap n) = 0) /\
  (stack_op_weight (SODup n) = 1) /\
  (stack_op_weight (SOPoke n op) = 0) /\
  (stack_op_weight (SOSpill n) = -1) /\
  (stack_op_weight (SORestore n) = 1) /\
  (stack_op_weight (SOEmit name) = 0) /\
  (stack_op_weight SOInitialFmp = 1) /\
  (stack_op_weight (SOLabel name) = 0) /\
  (stack_op_weight (SOPushLabel name) = 1) /\
  (stack_op_weight (SOPushOfst name n) = 1)
End

Definition trace_weight_def:
  (trace_weight [] = (0:int)) /\
  (trace_weight (x::xs) = stack_op_weight x + trace_weight xs)
End

Theorem trace_weight_append:
  !xs ys. trace_weight (xs ++ ys) = trace_weight xs + trace_weight ys
Proof
  Induct >> simp[trace_weight_def, INT_ADD_ASSOC]
QED

Definition regular_correction_def:
  regular_correction inst topics =
    &(LENGTH inst.inst_outputs) - &(LENGTH (compute_operands inst)) -
    trace_weight (FST (generate_emit_ops inst topics (init_plan_state 0)))
End

Theorem generate_emit_ops_stack:
  (SND (generate_emit_ops inst topics ps)).ps_stack = ps.ps_stack
Proof
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >~ [`venom_to_evm_name _ = SOME _`]
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[])) >>
  Cases_on `inst.inst_opcode = DJMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      Cases_on `HD inst.inst_operands` >> simp[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (gvs[] >> simp[generate_emit_ops_def, fresh_label_def]) >>
  Cases_on `inst.inst_opcode = LOG`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >> simp[generate_emit_ops_def]
QED

Theorem generate_emit_ops_weight:
  trace_weight (FST (generate_emit_ops inst topics ps)) =
  trace_weight (FST (generate_emit_ops inst topics qs))
Proof
  Cases_on `inst.inst_opcode = INITIAL_FMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `venom_to_evm_name inst.inst_opcode`
  >~ [`venom_to_evm_name _ = SOME _`] >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[trace_weight_def, stack_op_weight_def])) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      rpt (CASE_TAC >> gvs[trace_weight_def, stack_op_weight_def])) >>
  Cases_on `inst.inst_opcode = DJMP` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[] >> simp[generate_emit_ops_def] >>
      Cases_on `HD inst.inst_operands` >>
      simp[fresh_label_def, trace_weight_def, stack_op_weight_def]) >>
  Cases_on `inst.inst_opcode = RET` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (gvs[] >> simp[generate_emit_ops_def, fresh_label_def, trace_weight_def,
          stack_op_weight_def]) >>
  Cases_on `inst.inst_opcode = LOG` >- (gvs[] >> simp[generate_emit_ops_def]) >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >> simp[generate_emit_ops_def]
QED

(* INVOKE's two synthetic pushes are independent of its output arity. *)
Theorem regular_correction_invoke:
  inst.inst_opcode = INVOKE /\ HD inst.inst_operands = Label callee ==>
  regular_correction inst topics =
    &(LENGTH inst.inst_outputs) - &(LENGTH (compute_operands inst)) - 2
Proof
  strip_tac >>
  simp[regular_correction_def, generate_emit_ops_def, venom_to_evm_name_def,
       fresh_label_def, trace_weight_def, stack_op_weight_def] >>
  intLib.ARITH_TAC
QED

Theorem regular_correction_invoke_two_outputs:
  inst.inst_opcode = INVOKE /\ HD inst.inst_operands = Label callee /\
  LENGTH inst.inst_outputs = 2 ==>
  regular_correction inst topics = -(&(LENGTH (compute_operands inst)))
Proof
  strip_tac >> drule_all regular_correction_invoke >> simp[]
QED

Theorem push_outputs_length:
  !outs ps.
  LENGTH (FOLDL (\s out.
    s with ps_stack := stack_push (Var out) s.ps_stack) ps outs).ps_stack =
  LENGTH ps.ps_stack + LENGTH outs
Proof
  Induct >> simp[] >> simp[stack_push_def]
QED

Theorem regular_silent_core_balance:
  LENGTH (compute_operands inst) <= LENGTH ps4.ps_stack /\
  ps5 = ps4 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack /\
  ps6 = FOLDL (\s out.
    s with ps_stack := stack_push (Var out) s.ps_stack) ps5 inst.inst_outputs /\
  generate_emit_ops inst topics ps6 = (emit_ops, ps7) ==>
  &(LENGTH ps7.ps_stack) = &(LENGTH ps4.ps_stack) +
    trace_weight emit_ops + regular_correction inst topics
Proof
  strip_tac >>
  `ps7.ps_stack = ps6.ps_stack` by
    metis_tac[generate_emit_ops_stack, pairTheory.SND] >>
  `trace_weight emit_ops =
    trace_weight (FST (generate_emit_ops inst topics (init_plan_state 0)))` by
    metis_tac[generate_emit_ops_weight, pairTheory.FST] >>
  gvs[regular_correction_def, push_outputs_length, stack_pop_def,
      listTheory.LENGTH_TAKE] >>
  intLib.ARITH_TAC
QED
