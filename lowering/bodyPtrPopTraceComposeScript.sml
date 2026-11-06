Theory bodyPtrPopTraceCompose
Ancestors bodyPtrPopTraceInstruction bodyPtrPopTraceBoundary
  bodyPtrPopTraceReplay fragGasSeqPtr list rich_list

(* A bounded local replay only: no supported-entry or counted-path claim. *)
Theorem pop_trace_suffix_replay_aux[local]:
  !k n. n + k = 37 /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn [] (pop_trace_prov n) (pop_trace_taint n)
    (DROP n pop_saved_code) (pop_trace_state n)
    (pop_trace_prov 37) (pop_trace_taint 37)
Proof
  Induct_on `k`
  >- (rpt strip_tac >> gvs[] >>
      `DROP 37 pop_saved_code = []` by
        metis_tac[pop_trace_code_length, DROP_LENGTH_NIL] >>
      simp[inst_seq_ptr_def]) >>
  rpt strip_tac >>
  `n < 37 /\ n <= 37 /\ SUC n + k = 37` by decide_tac >>
  `DROP n pop_saved_code = pop_trace_inst n :: DROP (SUC n) pop_saved_code` by
    (`n < LENGTH pop_saved_code` by simp[pop_trace_code_length] >>
     drule HD_DROP >> strip_tac >>
     Cases_on `DROP n pop_saved_code` >>
     gvs[pop_trace_inst_def, DROP_SUC, LENGTH_DROP, pop_trace_code_length]) >>
  drule pop_trace_ghost_successor >> strip_tac >>
  simp[Once inst_seq_ptr_def, pop_trace_ptr_inst_ok, pop_trace_cursor] >>
  first_x_assum irule >> simp[]
QED

Theorem pop_trace_suffix_replay:
  n <= 37 /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn [] (pop_trace_prov n) (pop_trace_taint n)
    (DROP n pop_saved_code) (pop_trace_state n)
    (pop_trace_prov 37) (pop_trace_taint 37)
Proof
  strip_tac >> irule pop_trace_suffix_replay_aux >>
  conj_tac >- simp[] >> qexists_tac `37 - n` >> simp[]
QED

Theorem pop_trace_replay:
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn [] FEMPTY entry_taint pop_saved_code
    (pop_trace_state 0) (pop_trace_prov 37) (pop_trace_taint 37)
Proof
  strip_tac >>
  mp_tac (Q.INST [`n` |-> `0`] pop_trace_suffix_replay) >>
  simp[pop_trace_prov_def, pop_trace_taint_def]
QED
