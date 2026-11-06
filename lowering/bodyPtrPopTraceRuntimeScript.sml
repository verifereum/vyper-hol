Theory bodyPtrPopTraceRuntime
Ancestors bodyPtrPopTraceReplay exprLoweringProps instIdxIndep
  bodyPtrPopSavedExecution bodyPtrPopTraceBoundary vyperValue
  venomExecSemantics compileEnv list rich_list

Theorem pop_run_prefix_success:
  run_inst_seq code s = OK t ==>
  ?p. run_inst_seq (TAKE n code) s = OK p
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `DROP n code` mp_tac) >>
  simp[TAKE_DROP] >> metis_tac[]
QED

Theorem pop_run_prefix_next:
  run_inst_seq code s = OK t /\ n < LENGTH code ==>
  ?p q. run_inst_seq (TAKE n code) s = OK p /\
    run_inst_seq (TAKE (SUC n) code) s = OK q /\
    step_inst_base (EL n code) p = OK q
Proof
  strip_tac >>
  drule (Q.GEN `n` pop_run_prefix_success) >>
  disch_then (qspec_then `n` strip_assume_tac) >>
  `?q. run_inst_seq (TAKE (SUC n) code) s = OK q` by
    metis_tac[pop_run_prefix_success] >>
  `TAKE (SUC n) code = TAKE n code ++ [EL n code]` by
    simp[TAKE_SUC, TAKE1_DROP] >>
  qpat_assum `run_inst_seq (TAKE n code) s = OK p`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[EL n code]` mp_tac) >>
  simp[run_inst_seq_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `step_inst_base (EL n code) p` >> gvs[] >> metis_tac[]
QED

Theorem pop_run_prefix_cursor:
  run_inst_seq code s = OK t /\ n < LENGTH code /\
  EVERY (\i. ~is_terminator i.inst_opcode) code ==>
  ?p q u. run_inst_seq (TAKE n code) s = OK p /\
    run_inst_seq (TAKE (SUC n) code) s = OK q /\
    step_inst_base (EL n code) (p with vs_inst_idx := n) = OK u /\
    (u with vs_inst_idx := SUC n) = (q with vs_inst_idx := SUC n)
Proof
  strip_tac >> drule_all pop_run_prefix_next >> strip_tac >>
  `~is_terminator (EL n code).inst_opcode` by
    (fs[EVERY_MEM] >> first_x_assum irule >> simp[EL_MEM]) >>
  qexistsl_tac [`p`, `q`, `q with vs_inst_idx := n`] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem pop_trace_nonterminators:
  EVERY (\i. ~is_terminator i.inst_opcode) pop_saved_code
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_runtime_successor:
  n < 37 ==>
  ?u. step_inst_base (pop_trace_inst n) (pop_trace_state n) = OK u /\
    (u with vs_inst_idx := SUC n) = pop_trace_state (SUC n)
Proof
  strip_tac >> mp_tac pop_saved_runtime_index >> strip_tac >>
  `n < LENGTH pop_saved_code` by simp[pop_trace_code_length] >>
  mp_tac pop_trace_nonterminators >> strip_tac >>
  drule_all pop_run_prefix_cursor >> strip_tac >>
  simp[pop_trace_state_def, pop_trace_inst_def] >> metis_tac[]
QED
