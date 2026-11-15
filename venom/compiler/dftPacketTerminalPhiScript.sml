Theory dftPacketTerminalPhi
Ancestors
  gasOracleReplay venomExecSemantics venomInst stateEquiv

Theorem dft_packet_terminal_phis_gas:
  !fuel C i s post xs sp u gs k.
    is_terminator i.inst_opcode /\
    step_inst fuel C i s = OK post /\
    eval_phis post xs = OK sp /\
    u = s with vs_gas_readings := gs ==>
    ?v w. step_inst fuel C i u = OK v /\
      v = post with vs_gas_readings := gs /\
      eval_phis v xs = OK w /\
      (w with vs_inst_idx := k) =
        ((sp with vs_inst_idx := k) with vs_gas_readings := gs)
Proof
  rpt strip_tac >> gvs[] >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def]) >>
  `gas_replay_at 0 (step_inst fuel C i) s` by
    ((metis_tac[venomExecSemanticsTheory.step_inst_preserves_inst_idx, venomExecSemanticsTheory.step_inst_non_invoke, gasOracleReplayTheory.gas_base_non_gas, venomExecSemanticsTheory.step_inst_param_ok_or_error, gasOracleReplayTheory.gas_eval_phis, venomExecSemanticsTheory.step_inst_base_preserves_inst_idx, gasOracleReplayTheory.gas_exec_block, gasOracleReplayTheory.gas_step_inst, venomExecSemanticsTheory.eval_phis_def, venomExecSemanticsTheory.step_inst_def, venomInstTheory.is_terminator_def, gasOracleReplayTheory.gas_replay_at_def, venomInstTheory.recordtype_instruction_seldef_inst_opcode_def])) >>
  qpat_x_assum `gas_replay_at 0 _ _` mp_tac >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `step_inst fuel C i (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  qspecl_then [`xs`, `post`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `eval_phis (post with vs_gas_readings := gs) xs` >>
  gvs[lift_result_def]
QED
