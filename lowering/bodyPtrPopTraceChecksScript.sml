Theory bodyPtrPopTraceChecks
Ancestors bodyPtrPopTraceReplay bodyPtrPopTraceBoundary bodyPtrPopSavedExecution
  bodyPtrPopEmptyTaint ptrDiscipline contextCodegenRel codegenRel
  vyperValue finite_map list

Theorem pop_trace_code_empty_ranges:
  EVERY (\i. !s. source_memory_read_ranges i s = [] /\
    source_memory_write_ranges i s = []) pop_saved_code
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_empty_ranges:
  n < 37 ==> source_memory_read_ranges (pop_trace_inst n) s = [] /\
    source_memory_write_ranges (pop_trace_inst n) s = []
Proof
  strip_tac >> mp_tac pop_trace_code_empty_ranges >>
  simp[EVERY_MEM] >> strip_tac >> first_x_assum irule >>
  simp[pop_trace_inst_def, EL_MEM, pop_trace_code_length]
QED

Theorem pop_trace_access_ok:
  n < 37 ==> access_ok lo FEMPTY fn (pop_trace_inst n) s
Proof
  strip_tac >> drule pop_trace_empty_ranges >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  simp[access_ok_def]
QED

Theorem pop_trace_taint_ok:
  n < 37 ==> taint_ok fn (pop_trace_taint n) (pop_trace_inst n) s
Proof
  strip_tac >> `n <= 37` by decide_tac >>
  `!u m. FLOOKUP (pop_trace_taint n).t_var u = SOME m ==> m = {}` by
    (mp_tac (Q.SPEC `n` pop_trace_register_clean) >> simp[]) >>
  drule pop_op_taint_empty >> strip_tac >>
  drule pop_trace_empty_ranges >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  simp[taint_ok_def, pop_trace_storage_empty, pop_trace_transient_empty]
QED

Theorem pop_allocas_from_zero:
  allocas_from 0 s
Proof
  simp[allocas_from_def]
QED
