(* The shared LOG instruction boundary, after its operands are evaluated. *)
Theory logEmitStep
Ancestors
  venomExecSemantics venomState venomInst valueEncodingDefs words list

Theorem log_static_step:
  inst.inst_opcode = LOG /\ s.vs_call_ctx.cc_static /\
  IS_SOME (eval_operands inst.inst_operands s) ==>
  step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[step_inst_base_opcode_eqs]
QED

Theorem log_emit_static_step:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\ s.vs_call_ctx.cc_static ==>
  step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >> irule log_static_step >> simp[] >>
  `EVERY (\op. IS_SOME (eval_operand op s)) topic_ops` by
    simp[GSYM eval_operands_IS_SOME_EVERY] >>
  gvs[eval_operands_IS_SOME_EVERY, EVERY_MEM, MEM_REVERSE,
      eval_operand_def]
QED
