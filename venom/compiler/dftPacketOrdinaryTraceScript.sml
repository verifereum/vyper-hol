Theory dftPacketOrdinaryTrace
Ancestors
  dftGasFromListTraceDefs venomExecSemantics

Theorem dft_ordinary_trace_cons:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst f C inst s = OK post ==>
  dftGasFromListTraceDefs$trace_block p d g C fn bb s =
    ((p,d,inst.inst_id),fn,inst,s)::
    dftGasFromListTraceDefs$trace_block p d g C fn bb
      (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `step_inst g C inst s = OK post` by
    metis_tac[step_inst_non_invoke] >>
  drule trace_block_visit >>
  (simp[dftGasFromListTraceDefsTheory.trace_step_noninvoke])
QED
