Theory fnBlockPlanStaticBalance
Ancestors
  stackPlanGen stackPlanTypes asmIR integer

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
