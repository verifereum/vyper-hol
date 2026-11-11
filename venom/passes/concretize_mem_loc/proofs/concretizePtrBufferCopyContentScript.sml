Theory concretizePtrBufferCopyContent
Ancestors copyFwdEquiv allocaRemapDefs codegenRel venomExecSemantics
  venomState words list rich_list

Theorem ptr_payload_write_content:
  i < LENGTH bytes ==>
  read_byte (dst+i) (write_memory_with_expansion dst bytes s).vs_memory =
  read_byte (dt+i) (write_memory_with_expansion dt bytes t).vs_memory
Proof
  pure_rewrite_tac[read_byte_def, GSYM mem_byte_at_def] >>
  metis_tac[wmwe_byte_at_written]
QED

Theorem ptr_calldatacopy_content:
  inst.inst_opcode = CALLDATACOPY /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
  eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
  eval_operand nop s = SOME n /\ eval_operand nop t = SOME n /\
  s.vs_call_ctx.cc_calldata = t.vs_call_ctx.cc_calldata ==>
  ?s' t'. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK t' /\
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >> simp[step_inst_base_def] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Theorem ptr_codecopy_content:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
  eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
  eval_operand nop s = SOME n /\ eval_operand nop t = SOME n /\
  s.vs_code = t.vs_code ==>
  ?s' t'. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK t' /\
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >> simp[step_inst_base_def] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Theorem ptr_dloadbytes_content:
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
  eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
  eval_operand nop s = SOME n /\ eval_operand nop t = SOME n /\
  s.vs_data_section = t.vs_data_section ==>
  ?s' t'. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK t' /\
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >> simp[step_inst_base_def] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Theorem ptr_returndatacopy_content:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop s = SOME d /\ eval_operand dop t = SOME dt /\
  eval_operand sop s = SOME r /\ eval_operand sop t = SOME r /\
  eval_operand nop s = SOME n /\ eval_operand nop t = SOME n /\
  s.vs_returndata = t.vs_returndata /\
  w2n r + w2n n <= LENGTH s.vs_returndata ==>
  ?s' t'. step_inst_base inst s = OK s' /\
    step_inst_base inst t = OK t' /\
    (!i. i < w2n n ==>
      read_byte (w2n d+i) s'.vs_memory =
      read_byte (w2n dt+i) t'.vs_memory)
Proof
  strip_tac >> gvs[] >> simp[step_inst_base_def] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ptr_payload_write_content >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP]
QED

Theorem ptr_returndatacopy_success_bound:
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dop;sop;nop] /\
  eval_operand dop t = SOME dt /\ eval_operand sop t = SOME r /\
  eval_operand nop t = SOME n /\ step_inst_base inst t = OK t' ==>
  w2n r + w2n n <= LENGTH t.vs_returndata
Proof
  simp[step_inst_base_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
QED
