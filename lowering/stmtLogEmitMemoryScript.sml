(* Memory boundary for the final event instruction. *)
Theory stmtLogEmitMemory
Ancestors
  stmtSimLogEmit fragExecMem instMemFrontier emitHelperProps
  venomInst venomState memSafeRun words list

Theorem compile_log_emit_mem_ok:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  (w2n sz = 0 \/ w2n off + w2n sz <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule emitted_insts_emit_inst >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  mp_tac (Q.SPECL [`sa.cs_next_id`,`LENGTH (topic_ops:operand list)`,`REVERSE topic_ops`,
    `len_op`,`ptr_op`,`[]`,`s`] below_frontier_LOG) >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem compile_log_emit_frontier:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel H ctx func ce cx es s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule emitted_insts_emit_inst >> strip_tac >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
    w2n_n2w, REVERSE_APPEND, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
