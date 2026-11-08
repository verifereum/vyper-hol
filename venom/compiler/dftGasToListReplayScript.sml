Theory dftGasToListReplay
Ancestors
  dftGasToListAgreement dftGasToListTrace dftGasOracleDefs gasOracleReplay stateEquiv contextCodegenRel
  venomExecSemantics venomState o1PassContract list rich_list arithmetic

Definition residual_result_def:
  residual_result ws = lift_result
    (\a b. b = a with vs_gas_readings := ws)
    (\a b. b = a with vs_gas_readings := ws)
    (\a b. b = a with vs_gas_readings := ws)
End

Theorem residual_result_cases[simp]:
  residual_result ws (OK s) r <=> r = OK (s with vs_gas_readings := ws)
Proof
  Cases_on `r` >> simp[residual_result_def, lift_result_def]
QED

Theorem replay_zero_boundary:
  gas_replay_at 0 f s ==>
  residual_result ws (f s) (f (s with vs_gas_readings := ws))
Proof
  simp[gas_replay_at_def] >> strip_tac >>
  first_x_assum (qspec_then `ws` mp_tac) >>
  Cases_on `f s` >> Cases_on `f (s with vs_gas_readings := ws)` >>
  simp[residual_result_def, lift_result_def]
QED

Theorem replay_base_non_gas:
  inst.inst_opcode <> GAS ==>
  residual_result ws (step_inst_base inst s)
    (step_inst_base inst (s with vs_gas_readings := ws))
Proof
  strip_tac >> irule replay_zero_boundary >>
  irule gas_base_non_gas >> simp[]
QED

Theorem replay_phis:
  !insts s ws. residual_result ws (eval_phis s insts)
    (eval_phis (s with vs_gas_readings := ws) insts)
Proof
  rpt gen_tac >> qspecl_then [`insts`, `s`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `ws` mp_tac) >>
  Cases_on `eval_phis s insts` >>
  Cases_on `eval_phis (s with vs_gas_readings := ws) insts` >>
  simp[residual_result_def, lift_result_def]
QED

Theorem replay_gas:
  padded_reading ws 0 = w ==>
  residual_result (DROP 1 ws) (ev_gas w inst s)
    (exec_gas inst (s with vs_gas_readings := ws))
Proof
  strip_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[ev_gas_def, exec_gas_def, residual_result_def, lift_result_def] >>
  Cases_on `outs` >> simp[] >>
  Cases_on `ws` >> gvs[padded_reading_def, lift_result_def]
QED

Theorem trace_replay:
  (!orc p d fuel ctx inst s ws.
    agrees orc ws (trace_events (trace_step orc p d fuel ctx inst s)) ==>
    residual_result (DROP (LENGTH (trace_events (trace_step orc p d fuel ctx inst s))) ws)
      (ev_step orc p d fuel ctx inst s)
      (step_inst fuel ctx inst (s with vs_gas_readings := ws))) /\
  (!orc p d fuel ctx fn bb s ws.
    agrees orc ws (trace_events (trace_block orc p d fuel ctx fn bb s)) ==>
    residual_result (DROP (LENGTH (trace_events (trace_block orc p d fuel ctx fn bb s))) ws)
      (ev_block orc p d fuel ctx bb s)
      (exec_block fuel ctx bb (s with vs_gas_readings := ws))) /\
  (!orc p d fuel ctx fn s ws.
    agrees orc ws (trace_events (trace_blocks orc p d fuel ctx fn s)) ==>
    residual_result (DROP (LENGTH (trace_events (trace_blocks orc p d fuel ctx fn s))) ws)
      (ev_blocks orc p d fuel ctx fn s)
      (run_blocks fuel ctx fn (s with vs_gas_readings := ws)))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_replay[step]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[trace_step_eq, trace_events_def, agrees_cons,
           Once ev_step_def, step_inst_def, step_inst_base_def] >>
      strip_tac >> irule replay_gas >> simp[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[trace_step_eq, trace_events_def, Once ev_step_def, step_inst_def] >>
  irule replay_base_non_gas >> simp[]
QED
Resume trace_replay[invoke]:
  simp[trace_step_eq, Once ev_step_def, step_inst_def, gas_setup_callee] >>
  Cases_on `decode_invoke inst`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
  Cases_on `eval_operands pair1 s`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `eval_operands pair1 s = SOME args` >>
  Cases_on `setup_callee callee args s`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  gvs[] >> strip_tac >>
  first_x_assum drule >>
  Cases_on `ev_blocks orc ((d,inst.inst_id)::p) d fuel ctx callee cs` >>
  Cases_on `run_blocks fuel ctx callee (cs with vs_gas_readings := ws)` >>
  simp[residual_result_def, lift_result_def] >> strip_tac >> gvs[] >>
  simp[gas_merge_callee, gas_adopt_return, gas_bind_outputs] >>
  CASE_TAC >> simp[lift_result_def]
QED
Resume trace_replay[block]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  once_rewrite_tac[trace_block_eq, ev_block_def, exec_block_def] >>
  simp[] >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >> gvs[] >>
  Cases_on `ev_step orc p d fuel ctx inst s` >>
  simp[trace_events_def, trace_events_append, agrees_append] >>
  strip_tac >>
  qpat_x_assum `!ws. agrees orc ws (trace_events (trace_step _ _ _ _ _ _ _)) ==> _` drule >>
  Cases_on `step_inst fuel ctx inst (s with vs_gas_readings := ws)` >>
  simp[residual_result_def, lift_result_def] >> strip_tac >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (simp[trace_events_def] >> Cases_on `v.vs_halted` >> simp[lift_result_def]) >>
  gvs[] >> first_x_assum drule >>
  simp[residual_result_def, DROP_DROP_T, ADD_COMM]
QED
Resume trace_replay[blocks]:
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `fuel`
  >- simp[trace_blocks_zero, trace_events_def, Once ev_blocks_def,
           run_blocks_def, residual_result_def, lift_result_def] >>
  rename1 `SUC k` >>
  once_rewrite_tac[trace_blocks_eq, ev_blocks_def, run_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  gvs[] >>
  qspecl_then [`bb.bb_instructions`, `s`, `ws`] mp_tac replay_phis >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  Cases_on `eval_phis (s with vs_gas_readings := ws) bb.bb_instructions` >>
  gvs[residual_result_def, lift_result_def] >> strip_tac >> gvs[] >>
  simp[trace_events_def, lift_result_def] >>
  rewrite_tac[GSYM residual_result_def] >>
  qmatch_goalsub_abbrev_tac `ev_block orc p (SUC d) k ctx bb entry` >>
  Cases_on `ev_block orc p (SUC d) k ctx bb entry` >>
  gvs[trace_events_append, trace_events_def, agrees_append] >> strip_tac >>
  qpat_x_assum `!ws. agrees orc ws (trace_events (trace_block _ _ _ _ _ _ _ _)) ==> _` drule >>
  simp[Abbr `entry`] >>
  qmatch_goalsub_abbrev_tac `run_block_non_phis k ctx bb input` >>
  Cases_on `run_block_non_phis k ctx bb input` >>
  simp[residual_result_def, lift_result_def] >> strip_tac >> gvs[] >>
  Cases_on `v.vs_halted`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  gvs[] >> first_x_assum drule >>
  simp[residual_result_def, DROP_DROP_T, ADD_COMM]
QED
Finalise trace_replay

Theorem replay_function:
  agrees orc ws (trace_events (trace_function orc fuel ctx fn s)) ==>
  residual_result (DROP (LENGTH (trace_events (trace_function orc fuel ctx fn s))) ws)
    (ev_function orc fuel ctx fn s)
    (run_function fuel ctx fn (s with vs_gas_readings := ws))
Proof
  simp[trace_function_def, ev_function_def, run_function_def] >>
  Cases_on `fn_entry_label fn`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  simp[] >> strip_tac >> drule (cj 3 trace_replay) >> simp[]
QED

Theorem replay_context:
  agrees orc ws (trace_events (trace_context orc fuel ctx s)) ==>
  residual_result (DROP (LENGTH (trace_events (trace_context orc fuel ctx s))) ws)
    (ev_context orc fuel ctx s)
    (run_context fuel ctx (s with vs_gas_readings := ws))
Proof
  simp[trace_context_def, ev_context_def, run_context_def] >>
  Cases_on `ctx.ctx_entry`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[trace_events_def, residual_result_def, lift_result_def] >>
  simp[] >> strip_tac >> drule replay_function >> simp[]
QED

Theorem residual_result_gas_rel:
  residual_result ws r r' ==> gas_res_rel r' r
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[residual_result_def, lift_result_def, gas_res_rel_def, gas_variant_def] >>
  rpt strip_tac >> gvs[gas_variant_def]
QED

Theorem active_inst_gas_update[simp]:
  active_inst fn inst (s with vs_gas_readings := ws) <=> active_inst fn inst s
Proof
  simp[active_inst_def]
QED

Theorem enters_block_gas_update:
  enters_block fn s t ==>
  enters_block fn (s with vs_gas_readings := ws) (t with vs_gas_readings := ws)
Proof
  simp[enters_block_def] >> strip_tac >>
  qexists_tac `bb` >> simp[] >>
  qexists_tac `s_phi with vs_gas_readings := ws` >> simp[] >>
  qspecl_then [`bb.bb_instructions`, `s`, `ws`] mp_tac replay_phis >>
  simp[]
QED
