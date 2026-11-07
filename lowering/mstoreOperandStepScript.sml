Theory mstoreOperandStep
Ancestors venomInst venomExecSemantics venomState words

Theorem step_mstore_operands:
  eval_operand dst s = SOME a /\ eval_operand value s = SOME w ==>
  step_inst_base (mk_inst id MSTORE [dst; value] []) s =
    OK (mstore (w2n a) w s)
Proof
  strip_tac >> simp[mk_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  PURE_REWRITE_TAC[instruction_accfupds, combinTheory.K_THM, opcode_case_def,
    exec_write2_def, listTheory.list_case_def] >>
  asm_simp_tac (srw_ss()) []
QED
