(* Physical LOG operand order and the continuing event state relation. *)
Theory stmtSimLogEmit
Ancestors
  stmtSimLogEncodeFrame stmtSimLogTopics stmtSimLogDataRun stmtSimLogArgsRun
  stmtSimLogSource venomExecSemantics venomState venomInst loweringSlice
  compileEnv exprLoweringProps valueEncoding words list arithmetic extCallOracleStep
  emitHelper emitHelperProps

Theorem log_emit_step:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op] /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\ ~s.vs_call_ctx.cc_static ==>
  step_inst_base inst s = OK (s with vs_logs := s.vs_logs ++
    [<|logger := w2w s.vs_call_ctx.cc_address; topics := topics;
       data := mem_bytes_at (w2n off) (w2n sz) s.vs_memory |>])
Proof
  cheat
QED

Theorem log_append_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with logs := es.logs ++ [ev])
    (s with vs_logs := s.vs_logs ++ [ev])
Proof
  cheat
QED

Theorem compile_log_emit_run:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel ctx func cenv cx es s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics;
           data := mem_bytes_at (w2n off) (w2n sz) s.vs_memory |>]) t /\
    (t with vs_logs := s.vs_logs) = s
Proof
  cheat
QED
