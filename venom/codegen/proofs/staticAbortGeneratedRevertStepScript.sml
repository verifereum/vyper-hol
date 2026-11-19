Theory staticAbortGeneratedRevertStep
Ancestors
  fnFrameStepsRevertForwardDeep staticAbortTrace staticAbortStraight
  stackOpAsmSim asmSem stackOpSim words list arithmetic planExec asmIR

Theorem generated_revert_step_requests:
  asm_block_at prog s.as_pc [AsmOp "REVERT"] /\
  2 <= LENGTH s.as_stack ==>
  ?t. asm_steps lo o2pc prog 1 s = AsmRevert t /\
      t.as_requests = s.as_requests
Proof
  strip_tac >>
  `s.as_pc < LENGTH prog /\ EL s.as_pc prog = AsmOp "REVERT"` by
    fs[asm_block_at_cons] >>
  Cases_on `s.as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rewrite_tac[numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_revert, asm_revert_op_def]
QED
