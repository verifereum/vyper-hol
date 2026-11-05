Theory dftGasFromListLocator
Ancestors
  dftGasFromListTraceSuccessor dftGasFromListTraceExtend dftGasFromListLookup
  dftGasFromListTraceDefs contextRawReachable venomWf list

Theorem raw_reachable_trace_wf[local]:
  !s ctx fn inst t. raw_reachable s ctx fn inst t ==>
    EVERY wf_function ctx.ctx_functions ==>
    wf_function fn /\
    ?fuel p d. MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context fuel ctx s)
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      `wf_function fn` by metis_tac[lookup_wf_function] >>
      conj_tac >- simp[] >>
      drule_all trace_context_entry >>
      disch_then (qspec_then `0` strip_assume_tac) >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >> conj_tac >- simp[] >>
      drule_all trace_context_next >>
      disch_then (qspec_then `0` strip_assume_tac) >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >> conj_tac >- simp[] >>
      drule_all trace_context_block >>
      disch_then (qspec_then `0` strip_assume_tac) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME callee` >>
  `wf_function callee` by metis_tac[lookup_wf_function] >>
  conj_tac >- simp[] >> first_x_assum drule >> strip_tac >>
  drule_all trace_context_callee >>
  disch_then (qspec_then `0` strip_assume_tac) >> metis_tac[]
QED

Theorem raw_reachable_trace:
  EVERY wf_function ctx.ctx_functions /\ raw_reachable s ctx fn inst t ==>
  ?fuel p d. MEM ((p,d,inst.inst_id),fn,inst,t) (trace_context fuel ctx s)
Proof
  metis_tac[raw_reachable_trace_wf]
QED
