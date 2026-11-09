(* TOP-LEVEL: the LOG instruction emitted by statement lowering appends the
   concrete EVM event, in source topic order, with the requested memory bytes. *)
Theory eventEmitProps
Ancestors
  loweringStateRelDefs exprLoweringProps emitHelperProps emitHelper compileEnv context
  venomExecSemantics venomState venomInst vyperState
  list rich_list words
Libs wordsLib

Theorem step_LOG:
  !id topic_ops topics offset_op size_op off len ss.
    LENGTH topic_ops < dimword(:256) /\
    eval_operands topic_ops ss = SOME topics /\
    eval_operand offset_op ss = SOME off /\ eval_operand size_op ss = SOME len /\
    ~ss.vs_call_ctx.cc_static ==>
    step_inst_base
      (mk_inst id LOG
        (Lit (n2w (LENGTH topic_ops)) ::
          REVERSE topic_ops ++ [size_op;offset_op]) []) ss =
      OK (ss with vs_logs := ss.vs_logs ++
        [<|logger := w2w ss.vs_call_ctx.cc_address;
           topics := topics; data := read_memory (w2n off) (w2n len) ss|>])
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once step_inst_base_def, mk_inst_def, read_memory_def, eval_operand_def,
    REVERSE_APPEND]
QED

Theorem emit_inst_LOG_correct:
  !cs cs' topic_ops topics offset_op size_op off len ss.
    emit_inst LOG
      (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [size_op;offset_op])
      [] cs = ((),cs') /\
    LENGTH topic_ops < dimword(:256) /\
    eval_operands topic_ops ss = SOME topics /\
    eval_operand offset_op ss = SOME off /\ eval_operand size_op ss = SOME len /\
    ~ss.vs_call_ctx.cc_static /\ fresh_vars_wrt cs ss ==>
    run_inst_seq (emitted_insts cs cs') ss =
      OK (ss with vs_logs := ss.vs_logs ++
        [<|logger := w2w ss.vs_call_ctx.cc_address;
           topics := topics; data := read_memory (w2n off) (w2n len) ss|>]) /\
    same_blocks cs cs' /\
    cs'.cs_current_insts = cs.cs_current_insts ++ emitted_insts cs cs' /\
    fresh_vars_wrt cs'
      (ss with vs_logs := ss.vs_logs ++
        [<|logger := w2w ss.vs_call_ctx.cc_address;
           topics := topics; data := read_memory (w2n off) (w2n len) ss|>])
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  drule emit_inst_extends >> strip_tac >> simp[same_blocks_def] >>
  conj_tac
  >- (irule run_inst_seq_sing_ok >>
      mp_tac (Q.SPECL [`cs.cs_next_id`, `topic_ops`, `topics`, `offset_op`,
        `size_op`, `off`, `len`, `ss`] step_LOG) >> simp[]) >>
  fs[fresh_vars_wrt_def, lookup_var_def]
QED

Theorem state_rel_simple_append_event:
  !cenv cx es ss ev.
    state_rel_simple cenv cx es ss ==>
    state_rel_simple cenv cx (es with logs := es.logs ++ [ev])
      (ss with vs_logs := ss.vs_logs ++ [ev])
Proof
  rpt gen_tac >> strip_tac >>
  fs[state_rel_simple_def, vars_rel_def, storage_rel_def, transient_rel_def,
    immutables_rel_simple_def, logs_rel_def, log_entry_equiv_def,
    LIST_REL_APPEND_suff, contract_storage_def, contract_transient_def] >>
  first_assum ACCEPT_TAC
QED
