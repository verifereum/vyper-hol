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
  strip_tac >> simp[step_inst_base_opcode_eqs, w2n_n2w, REVERSE_APPEND,
    mem_bytes_at_def]
QED

Theorem log_append_stmt_state_rel:
  stmt_state_rel ctx func cenv cx es s ==>
  stmt_state_rel ctx func cenv cx (es with logs := es.logs ++ [ev])
    (s with vs_logs := s.vs_logs ++ [ev])
Proof
  simp[stmt_state_rel_def, state_rel_def, logs_rel_eq,
    local_ptrs_rel_def, storage_rel_def, transient_rel_def,
    accounts_rel_def, contract_storage_def, contract_transient_def,
    immutables_rel_def, immutable_alloca_sep_def, local_region_def,
    lookup_var_def, local_backed_def, venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def,
    alloca_room_def, pending_alloca_size_def, fmp_room_def,
    immutable_base_zero_alt] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
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
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `~s.vs_call_ctx.cc_static` by gvs[stmt_state_rel_def, state_rel_def] >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id LOG
      (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) []]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND] >> strip_tac >>
     gvs[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `step_inst_base (mk_inst sa.cs_next_id LOG
      (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) []) s =
    OK (s with vs_logs := s.vs_logs ++
      [<|logger := w2w cx.txn.target; topics := topics;
         data := mem_bytes_at (w2n off) (w2n sz) s.vs_memory |>])` by
    (qpat_x_assum `s.vs_call_ctx.cc_address = _` (fn th => rewrite_tac[GSYM th]) >>
     irule log_emit_step >> simp[mk_inst_def]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[GSYM APPEND_ASSOC] >> strip_tac >>
  simp[Once run_inst_seq_def] >> simp[run_inst_seq_def] >>
  irule log_append_stmt_state_rel >> simp[]
QED
