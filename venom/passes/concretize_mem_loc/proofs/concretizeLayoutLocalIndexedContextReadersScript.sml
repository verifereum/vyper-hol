Theory concretizeLayoutLocalIndexedContextReaders
Ancestors concretizeLayoutLocalContextReaders concretizeLayoutReaderContext
  frameRelocationGuardedValues
  frameRelocationEnvironment venomExecSemantics venomState

Definition indexed_context_read_opcode_def:
  indexed_context_read_opcode op <=> MEM op [BLOCKHASH; BLOBHASH]
End

Theorem indexed_context_reader_execution:
  indexed_context_read_opcode inst.inst_opcode /\
  inst.inst_operands = [arg] /\ inst.inst_outputs = [v] /\
  relocation_reader_context s t /\ eval_operand arg s = eval_operand arg t /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t)
Proof
  simp[indexed_context_read_opcode_def] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_read1_def] >>
  Cases_on `eval_operand arg t` >> gvs[] >>
  strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[exec_read1_def, relocation_reader_context_def] >> metis_tac[]
QED

