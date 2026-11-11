(* Observable mismatch only; the full frozen-premise audit is separate. *)
Theory internalReturnCopyFwdHaltObservable
Ancestors
  internalReturnCopyFwdHaltProbe ptrDiscipline venomExecSemantics
  venomState words list passSimulationDefs venomMemProps

Theorem ircf_halt_observable_terminates:
  terminates (run_block 0 ircf_halt_probe_ctx ircf_halt_probe_bb
    (ircf_halt_probe_state q (0w:word8)))
Proof
  strip_assume_tac (Q.INST [`k` |-> `0`, `s` |-> `q`,
    `b` |-> `0w:word8`] ircf_halt_probe_run) >> simp[terminates_def]
QED

Theorem ircf_halt_observable_address:
  run_block k ircf_halt_probe_ctx ircf_halt_probe_bb
    (ircf_halt_probe_state q b) = Halt r ==>
  r.vs_call_ctx.cc_address = q.vs_call_ctx.cc_address
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> strip_tac >> gvs[]
QED

Theorem ircf_halt_observable_words:
  ~word_agree_except {}
    (word_of_bytes T (0w:bytes32) (REPLICATE 32 (0w:word8)))
    (word_of_bytes T (0w:bytes32) (REPLICATE 32 (1w:word8)))
Proof
  simp[word_agree_except_def, word_bytes_roundtrip_256] >>
  qexists_tac `0` >> simp[rich_listTheory.REPLICATE_compute]
QED

Theorem ircf_halt_observable_mismatch:
  !m. ~dead_result_rel
    <|d_stor := (\a st. {}); d_trans := (\a st. {});
      d_imm := (\im. {}); d_ret := (\r. {})|>
    (run_block 0 ircf_halt_probe_ctx ircf_halt_probe_bb
      (ircf_halt_probe_state q (0w:word8)))
    (run_block m ircf_halt_probe_ctx ircf_halt_probe_bb
      (ircf_halt_probe_state q (1w:word8)))
Proof
  gen_tac >>
  strip_assume_tac (Q.INST [`k` |-> `0`, `s` |-> `q`,
    `b` |-> `0w:word8`] ircf_halt_probe_run) >>
  strip_assume_tac (Q.INST [`k` |-> `m`, `s` |-> `q`,
    `b` |-> `1w:word8`] ircf_halt_probe_run) >>
  imp_res_tac ircf_halt_observable_address >>
  strip_tac >> gvs[dead_result_rel_def] >>
  qpat_x_assum `accounts_agree_except _ _ _` mp_tac >>
  simp[accounts_agree_except_def, storage_agree_except_def, key_taint_def] >>
  qexists_tac `q.vs_call_ctx.cc_address` >> strip_tac >>
  qexists_tac `0w` >> simp[ircf_halt_observable_words]
QED
