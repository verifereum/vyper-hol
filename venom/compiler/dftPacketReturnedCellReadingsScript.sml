Theory dftPacketReturnedCellReadings
Ancestors
  frameInvokeReturn gasOracleReplay venomExecSemantics venomState sorting

Theorem dft_packet_returned_cell_readings:
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\
  setup_callee ctf args b0 = SOME ent /\
  run_blocks n C8 ctf ent = IntRet ir out /\
  bind_outputs c.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state b0 out)) = SOME bound /\
  step_inst n C8 c b0 = OK post /\
  PERM (MAP THE (FILTER IS_SOME child_mask) ++ out.vs_gas_readings)
    ent.vs_gas_readings ==>
  PERM (MAP THE (FILTER IS_SOME child_mask) ++ post.vs_gas_readings)
    b0.vs_gas_readings
Proof
  strip_tac >>
  drule_all_then assume_tac (cj 1 matched_run_invoke_return) >>
  `bound = post` by
    (qpat_x_assum `step_inst _ _ _ _ = OK bound` mp_tac >> simp[]) >>
  drule_then assume_tac gas_setup_callee_readings >>
  drule gas_bind_outputs_readings >> gvs[]
QED
