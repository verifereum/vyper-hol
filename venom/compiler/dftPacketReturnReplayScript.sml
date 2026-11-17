Theory dftPacketReturnReplay
Ancestors
  dftPacketCalleeAlignment dftGasToListReplay dftGasFromListTraceDefs
  dftIndexedExec gasOracleReplay gasEvents frameGasEvents
  removeUnusedGasProofs dftGasFromListReadings stateEquiv gasCount passSimulationDefs
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem return_invoke_aligned[local]:
  LENGTH ks = LENGTH gs /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME child /\
  (!tail. eval_operands ops (u with vs_gas_readings := gs ++ tail) = SOME args /\
    setup_callee child args (u with vs_gas_readings := gs ++ tail) =
      SOME (entry with vs_gas_readings := gs ++ tail)) /\
  (!tail.
    (?extra. es = gas_events_blocks f C child
      (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
    (terminates (run_blocks f C child (entry with vs_gas_readings := gs ++ tail)) ==>
      residual_result tail (IntRet ir out)
        (run_blocks f C child (entry with vs_gas_readings := gs ++ tail)) /\
      gas_events_blocks f C child (entry with vs_gas_readings := gs ++ tail) = es) /\
    (!ret v. run_blocks f C child (entry with vs_gas_readings := gs ++ tail) = IntRet ret v ==>
      trace_gas (trace_blocks ((e,c.inst_id)::a) e f C child
        (entry with vs_gas_readings := gs ++ tail)) = ZIP (ks,gs))) ==>
  (!tail. ?extra. es = gas_events_step f C owner c
    (u with vs_gas_readings := gs ++ tail) ++ extra) /\
  (!tail v. step_inst f C c (u with vs_gas_readings := gs ++ tail) = OK v ==>
    gas_events_step f C owner c (u with vs_gas_readings := gs ++ tail) = es /\
    v.vs_gas_readings = tail /\
    trace_gas (trace_step a e f C fn c (u with vs_gas_readings := gs ++ tail)) = ZIP (ks,gs) /\
    (!tail'. step_inst f C c (u with vs_gas_readings := gs ++ tail') =
      OK (v with vs_gas_readings := tail') /\
      gas_events_step f C owner c (u with vs_gas_readings := gs ++ tail') = es))
Proof
  strip_tac >> conj_tac
  >- ((gen_tac >> simp[Once gas_events_defs] >> (gvs[]))) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail. eval_operands _ _ = _ /\ _` (qspec_then `tail` strip_assume_tac) >>
  fs[gas_eval_operands] >>
  `?ret v0. run_blocks f C child (entry with vs_gas_readings := gs ++ tail) = IntRet ret v0 /\
    bind_outputs c.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (u with vs_gas_readings := gs ++ tail) v0)) = SOME v` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[Once run_defs] >>
     Cases_on `run_blocks f C child (entry with vs_gas_readings := gs ++ tail)` >>
     simp[] >> Cases_on `bind_outputs c.inst_outputs i.iret_values
       (adopt_return_fmp i (merge_callee_state (u with vs_gas_readings := gs ++ tail) v'))` >> simp[] >>
     metis_tac[]) >>
  `trace_gas (trace_blocks ((e,c.inst_id)::a) e f C child
      (entry with vs_gas_readings := gs ++ tail)) = ZIP (ks,gs)` by metis_tac[] >>
  `gas_count_blocks f C child (entry with vs_gas_readings := gs ++ tail) = LENGTH gs` by
    (mp_tac (cj 3 trace_gas_lengths) >>
     disch_then (qspecl_then [`(e,c.inst_id)::a`,`e`,`f`,`C`,`child`,
       `entry with vs_gas_readings := gs ++ tail`] mp_tac) >>
     simp[LENGTH_ZIP]) >>
  `gas_replay_at (LENGTH gs) (run_blocks f C child)
      (entry with vs_gas_readings := gs ++ tail)` by
    (qpat_assum `gas_count_blocks _ _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
     irule remove_unused_blocks_successful_replay_count >> simp[]) >>
  `!rest. run_blocks f C child (entry with vs_gas_readings := gs ++ rest) =
    IntRet ir (out with vs_gas_readings := rest) /\
    gas_events_blocks f C child (entry with vs_gas_readings := gs ++ rest) = es` by
    (gen_tac >>
     `LENGTH gs - (LENGTH gs + LENGTH tail) = 0` by decide_tac >>
     qpat_assum `gas_replay_at _ _ _` (mp_tac o Q.SPEC `rest` o REWRITE_RULE[gas_replay_at_def]) >>
     simp[gas_prefix_def, TAKE_APPEND, lift_result_def] >>
     Cases_on `run_blocks f C child (entry with vs_gas_readings := gs ++ rest)` >>
     simp[lift_result_def] >> strip_tac >>
     qpat_x_assum `!tail. (?extra. _) /\ _` (qspec_then `rest` mp_tac) >>
     simp[terminates_def, residual_result_def, lift_result_def] >> strip_tac >> gvs[]) >>
  qpat_assum `!rest. run_blocks _ _ _ _ = _ /\ _` (qspec_then `tail` strip_assume_tac) >>
  gvs[gas_merge_callee, gas_adopt_return, gas_bind_outputs, AllCaseEqs()] >>
  `x.vs_gas_readings = (adopt_return_fmp ir (merge_callee_state u out)).vs_gas_readings` by
    metis_tac[gas_bind_outputs_readings] >>
  simp[Once gas_events_defs, Once trace_defs] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> simp[Once run_defs, Once gas_events_defs, gas_merge_callee,
    gas_adopt_return, gas_bind_outputs]
QED
