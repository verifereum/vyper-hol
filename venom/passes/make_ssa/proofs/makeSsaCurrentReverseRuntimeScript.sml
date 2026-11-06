Theory makeSsaCurrentReverseRuntime
Ancestors
  o1FrameLockstep venomExecSemantics

Theorem current_step_copy_not_abort:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = NOP) ==>
  step_inst fuel C inst st <> Abort a t
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED
