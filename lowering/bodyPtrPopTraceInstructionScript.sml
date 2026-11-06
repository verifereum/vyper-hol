Theory bodyPtrPopTraceInstruction
Ancestors bodyPtrPopTraceChecks bodyPtrPopTraceRuntime bodyPtrPopTraceReplay
  bodyPtrPopTraceBoundary bodyPtrPopSavedExecution ptrSafeRun ptrDiscipline
  venomExecSemantics vyperValue list

Theorem pop_trace_code_no_invoke:
  EVERY (\i. i.inst_opcode <> INVOKE) pop_saved_code
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_no_invoke:
  n < 37 ==> (pop_trace_inst n).inst_opcode <> INVOKE
Proof
  strip_tac >> mp_tac pop_trace_code_no_invoke >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
  simp[pop_trace_inst_def, EL_MEM, pop_trace_code_length]
QED

Theorem pop_trace_step_success:
  n < 37 ==> ?u. step_inst fuel ctx (pop_trace_inst n) (pop_trace_state n) = OK u
Proof
  strip_tac >> drule pop_trace_no_invoke >> strip_tac >>
  simp[step_inst_non_invoke] >> metis_tac[pop_trace_runtime_successor]
QED

Theorem pop_trace_ptr_inst_ok:
  n < 37 /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn (pop_trace_prov n) (pop_trace_taint n)
    (pop_trace_inst n) (pop_trace_state n)
Proof
  strip_tac >> `n <= 37` by decide_tac >>
  drule pop_trace_step_success >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  simp[ptr_inst_ok_def, pop_trace_prov_empty, pop_trace_access_ok,
    pop_trace_taint_ok, pop_allocas_from_zero,
    pop_trace_storage_empty, pop_trace_transient_empty]
QED
