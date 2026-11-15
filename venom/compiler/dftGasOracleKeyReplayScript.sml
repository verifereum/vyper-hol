Theory dftGasOracleKeyReplay
Ancestors
  dftGasToListReplay dftGasToListAgreement dftGasToListTrace
  dftGasFromListTraceDefs dftGasFromListReadings
  dftGasOracleDefs gasOracleReplay contextCodegenRel
  stateEquiv venomExecProofs venomExecSemantics venomState venomInst list rich_list arithmetic

(* Key projection follows the actual oracle run, including stopped children. *)
Theorem oracle_native_trace_keys:
  (!orc p d fuel ctx inst s. !ws fn.
    agrees orc ws (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)) ==>
    MAP FST (visit_gas ((p,d,inst.inst_id),fn,inst,s with vs_gas_readings := ws) ++
      trace_gas (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst
        (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)) /\
  (!orc p d fuel ctx fn bb s. !ws.
    agrees orc ws (trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) ==>
    MAP FST (trace_gas (dftGasFromListTraceDefs$trace_block p d fuel ctx fn bb
      (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_block orc p d fuel ctx fn bb s)) /\
  (!orc p d fuel ctx fn s. !ws.
    agrees orc ws (trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s)) ==>
    MAP FST (trace_gas (dftGasFromListTraceDefs$trace_blocks p d fuel ctx fn
      (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_blocks orc p d fuel ctx fn s))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume oracle_native_trace_keys[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[trace_step_eq, Once dftGasFromListTraceDefsTheory.trace_defs,
       visit_gas_def, trace_events_def] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[trace_events_def]
QED

Resume oracle_native_trace_keys[invoke]:
  simp[trace_step_eq, Once dftGasFromListTraceDefsTheory.trace_defs,
       visit_gas_def, gas_eval_operands, gas_setup_callee, trace_events_def] >>
  Cases_on `decode_invoke inst` >> simp[trace_events_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[trace_events_def] >>
  rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[trace_events_def] >>
  rename1 `eval_operands pair1 s = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[trace_events_def] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  simp[gas_setup_callee] >> metis_tac[]
QED

Resume oracle_native_trace_keys[block]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[trace_block_eq, dftGasFromListTraceDefsTheory.trace_defs] >> simp[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[trace_gas_def, trace_events_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  simp[trace_gas_cons, trace_gas_append, MAP_APPEND, trace_events_def,
       trace_events_append] >> strip_tac >>
  `agrees orc ws (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))` by
    (fs[trace_events_append, agrees_append]) >>
  `MAP FST (visit_gas ((p,d,inst.inst_id),fn,inst,s with vs_gas_readings := ws) ++
      trace_gas (dftGasFromListTraceDefs$trace_step p d fuel ctx fn inst
        (s with vs_gas_readings := ws))) =
    trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s)` by
    metis_tac[] >>
  `residual_result
      (DROP (LENGTH (trace_events (dftGasToListTrace$trace_step orc p d fuel ctx inst s))) ws)
      (ev_step orc p d fuel ctx inst s)
      (step_inst fuel ctx inst (s with vs_gas_readings := ws))` by
    metis_tac[cj 1 dftGasToListReplayTheory.trace_replay] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >>
  Cases_on `step_inst fuel ctx inst (s with vs_gas_readings := ws)` >>
  gvs[residual_result_def, lift_result_def, MAP_APPEND, trace_events_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[trace_events_def, agrees_append] >>
  metis_tac[]
QED

Resume oracle_native_trace_keys[blocks]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `fuel`
  >- simp[dftGasFromListTraceDefsTheory.trace_blocks_zero,
           dftGasToListTraceTheory.trace_blocks_zero, trace_gas_def, trace_events_def] >>
  rename1 `SUC k` >>
  once_rewrite_tac[dftGasToListTraceTheory.trace_blocks_eq,
                   dftGasFromListTraceDefsTheory.trace_defs] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[trace_gas_def, trace_events_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`bb.bb_instructions`, `s`, `ws`] mp_tac replay_phis >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  Cases_on `eval_phis (s with vs_gas_readings := ws) bb.bb_instructions` >>
  gvs[residual_result_def, lift_result_def, trace_events_def] >> strip_tac >>
  gvs[trace_events_def] >>
  simp[trace_gas_append, MAP_APPEND, trace_events_append, agrees_append] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `ev_block orc p (SUC d) k ctx bb entry` >>
  `residual_result
      (DROP (LENGTH (trace_events (dftGasToListTrace$trace_block orc p (SUC d) k ctx fn bb entry))) ws)
      (ev_block orc p (SUC d) k ctx bb entry)
      (exec_block k ctx bb (entry with vs_gas_readings := ws))` by
    (irule (cj 2 dftGasToListReplayTheory.trace_replay) >> simp[Abbr `entry`]) >>
  Cases_on `ev_block orc p (SUC d) k ctx bb entry` >>
  Cases_on `exec_block k ctx bb (entry with vs_gas_readings := ws)` >>
  gvs[residual_result_def, lift_result_def, trace_gas_append, MAP_APPEND,
      trace_events_def, trace_events_append, agrees_append, Abbr `entry`] >>
  rename1 `ev_block orc p (SUC d) k ctx bb _ = OK out` >>
  Cases_on `out.vs_halted` >> gvs[trace_events_def] >> metis_tac[]
QED

Finalise oracle_native_trace_keys
