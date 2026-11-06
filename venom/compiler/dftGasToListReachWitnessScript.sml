Theory dftGasToListReachWitness
Ancestors
  dftGasToListVisitContinue dftGasToListVisitEdge dftGasToListReachTrace
  dftGasToListTrace dftGasOracleDefs contextCodegenRel venomExecProofs
  venomExecSemantics venomInst venomWf list

Theorem trace_context_eventual_continuation:
  EVERY wf_function ctx.ctx_functions /\
  MEM v (trace_context orc fuel ctx s) /\ visit_edge orc ctx v w tag ==>
  !bound. ?larger. fuel <= larger /\ bound <= larger /\
    MEM w (trace_context orc larger ctx s)
Proof
  strip_tac >> gen_tac >>
  Cases_on `ctx.ctx_entry` >> gvs[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >> gvs[] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME entry` >>
  Cases_on `fn_entry_label entry` >> gvs[trace_function_def] >>
  `wf_function entry` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  drule_all trace_blocks_eventual_continuation >>
  disch_then (qspec_then `bound` strip_assume_tac) >>
  qexists_tac `larger` >> simp[]
QED

Theorem ev_reachable_trace_item:
  !orc s ctx p d fn inst t. ev_reachable orc s ctx p d fn inst t ==>
  EVERY wf_function ctx.ctx_functions ==>
  ?fuel. MEM (TraceVisit p d fn inst t) (trace_context orc fuel ctx s)
Proof
  ho_match_mp_tac ev_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "jump"
  >> suspend "callee"
QED

Resume ev_reachable_trace_item[entry]:
  rpt strip_tac >>
  `wf_function fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all trace_context_entry_visit >>
  disch_then (qspecl_then [`orc`,`0`] mp_tac) >>
  metis_tac[trace_visit_member]
QED
Resume ev_reachable_trace_item[next]:
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `visit_edge orc ctx (TraceVisit p d fn inst t)
     (TraceVisit p d fn inst' (s' with vs_inst_idx := SUC t.vs_inst_idx)) NONE`
    by (irule (cj 1 visit_edge_rules) >> metis_tac[]) >>
  drule_all trace_context_eventual_continuation >> metis_tac[]
QED
Resume ev_reachable_trace_item[jump]:
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `visit_edge orc ctx (TraceVisit p d fn inst t)
     (TraceVisit p (SUC d) fn inst' t') (SOME(p,d,fn,s'))`
    by (irule (cj 2 visit_edge_rules) >> metis_tac[]) >>
  drule_all trace_context_eventual_continuation >> metis_tac[]
QED
Resume ev_reachable_trace_item[callee]:
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  `visit_edge orc ctx (TraceVisit p d fn inst t)
     (TraceVisit ((d,inst.inst_id)::p) (SUC d) fn' inst' t') NONE`
    by (irule (cj 3 visit_edge_rules) >> metis_tac[]) >>
  drule_all trace_context_eventual_continuation >> metis_tac[]
QED
Finalise ev_reachable_trace_item

Theorem ev_reachable_trace_witness:
  EVERY wf_function ctx.ctx_functions /\ ev_reachable orc s ctx p d fn inst t ==>
  ?fuel n. MEM (n,p,d,fn,inst,t) (trace_visits 0 (trace_context orc fuel ctx s))
Proof
  metis_tac[ev_reachable_trace_item, trace_visit_member]
QED
