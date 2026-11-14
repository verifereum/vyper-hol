Theory dftGasFromListContextReach
Ancestors
  dftGasFromListTraceReach dftGasFromListTraceDefs dftGasFromListRestore
  dftGasOracleDefs contextCodegenRel venomExecSemantics venomState list

Theorem trace_context_prefix_reachable:
  k < LENGTH (trace_context fuel ctx s) /\
  EL k (trace_context fuel ctx s) = ((p,d,id),fn,inst,t) /\
  trace_agrees orc (TAKE k (trace_context fuel ctx s)) ==>
  ev_reachable orc s ctx p d fn inst (t with vs_gas_readings := s.vs_gas_readings)
Proof
  Cases_on `ctx.ctx_entry` >- simp[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[trace_context_def] >>
  rename1 `lookup_function _ _ = SOME entry_fn` >>
  Cases_on `fn_entry_label entry_fn`
  >- simp[trace_context_def, trace_function_def] >>
  rename1 `fn_entry_label entry_fn = SOME lbl` >>
  simp[trace_context_def, trace_function_def] >> strip_tac >>
  qspecl_then [`[]`,`0`,`fuel`,`ctx`,`entry_fn`,
    `s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`,
    `orc`,`s`,`s.vs_gas_readings`] mp_tac (cj 3 trace_prefix_visits_reachable) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      `enters_block entry_fn
        (s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
        (u with vs_gas_readings := s.vs_gas_readings)` by
        (drule enters_block_restore >>
         disch_then (qspec_then `s.vs_gas_readings` mp_tac) >> simp[]) >>
      `active_inst entry_fn i (u with vs_gas_readings := s.vs_gas_readings)` by
        simp[active_inst_restore] >>
      irule ev_reachable_entry >> simp[] >> metis_tac[]) >>
  disch_then (qspecl_then [`k`,`p`,`d`,`id`,`fn`,`inst`,`t`] mp_tac) >> simp[]
QED

Theorem trace_context_reachable:
  trace_agrees orc (trace_context fuel ctx s) /\
  MEM ((p,d,id),fn,inst,t) (trace_context fuel ctx s) ==>
  ev_reachable orc s ctx p d fn inst (t with vs_gas_readings := s.vs_gas_readings)
Proof
  strip_tac >> fs[MEM_EL] >>
  rename1 `idx < LENGTH (trace_context fuel ctx s)` >>
  `trace_agrees orc (TAKE idx (trace_context fuel ctx s))` by
    metis_tac[dftGasFromListReplayBoundaryTheory.trace_agrees_take] >>
  metis_tac[trace_context_prefix_reachable]
QED
