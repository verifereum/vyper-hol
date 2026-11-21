(* Successful Log suffixes use the checked store/encoder and LOG boundaries. *)
Theory stmtSimLogSuffix
Ancestors
  stmtSimLogStoreCompose stmtSimLogEmit stmtSimLogTrace stmtSimLogTopics
  compileEnv loweringStateRelDefs exprLoweringProps emitHelperProps venomExecSemantics venomState
  valueEncoding valueEncodingDefs words list arithmetic stmtSimLogTopicFresh stmtSimLogSourceAllocate
  exprSimWordArgs stmtSimLogArgs fragExec stmtLowering stmtSimLogStoreEncode
  stmtSimLogDataRun abiEncoderCounters abiDecoderReentry abiEncoderAppend
  loweringHalt vyperABI contractABI abiBuiltinAllocation

Theorem log_emit_continuation:
  ~cx.txn.is_static /\
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\
  mem_bytes_at (w2n off) (w2n sz) s.vs_memory = data /\
  stmt_state_rel H ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel H ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := data |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  strip_tac >> drule_all compile_log_emit_run >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `t.vs_vars = s.vs_vars` by
    (qpat_x_assum `(t with vs_logs := _) = s`
      (mp_tac o Q.AP_TERM `\u. u.vs_vars`) >> simp[]) >>
  `fresh_vars_wrt limit_st t` by gvs[fresh_vars_wrt_def] >>
  `inst_extends sa sb` by (drule inst_extends_emit_inst >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `(t with vs_logs := _) = s`
      (mp_tac o Q.AP_TERM `\u. u.vs_labels`) >> simp[]) >>
  qexists_tac `t` >> gvs[] >>
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem log_emit_empty_suffix:
  ~cx.txn.is_static /\
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [Lit 0w;Lit 0w]) [] sa =
      ((),sb) /\ LENGTH topic_ops < dimword (:256) /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel H ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel H ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  strip_tac >> irule log_emit_continuation >> simp[] >>
  qexistsl_tac [`Lit 0w`,`0w`,`Lit 0w`,`0w`,`topic_ops`] >>
  gvs[eval_operand_def, mem_bytes_at_def]
QED

Theorem log_emit_encoded_suffix:
  ~cx.txn.is_static /\
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\ LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  eval_operand len_op s = SOME (n2w (LENGTH data)) /\
  b < dimword (:256) /\ LENGTH data < dimword (:256) /\
  mem_bytes_at b (LENGTH data) s.vs_memory = data /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel H ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel H ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := data |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  strip_tac >> irule log_emit_continuation >> simp[] >>
  qexistsl_tac [`len_op`,`n2w b`,`ptr_op`,`n2w (LENGTH data)`,`topic_ops`] >>
  gvs[w2n_n2w]
QED

Theorem log_operands_values:
  !ops ws. LIST_REL (\op w. eval_operand op s = SOME w) ops ws ==>
    eval_operands ops s = SOME ws
Proof
  Induct >> Cases_on `ws` >> simp[eval_operands_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED
