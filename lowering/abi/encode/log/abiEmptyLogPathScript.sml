(* TOP-LEVEL: actual Log statement lowering with no non-indexed fields emits
   the evaluated topics and empty data, preserving memory and external state. *)
Theory abiEmptyLogPath
Ancestors
  abiLogStmtCode abiLogEmit abiStateFrame typedCopyStateFrame stmtLowering compileEnv
  fragExec fragBlockPath venomState list words

Theorem compile_log_empty_data_path:
  !ctx func cenv lctx ty event_id args cs cs' sig_hash arg_types flags eval_ops eval_cut
    raw_topics topic_ops topic_cut topics ss.
    cenv.ce_event_info (nsid_to_string event_id) = SOME (sig_hash,arg_types,flags) /\
    compile_log_eval_all cenv args cs = (eval_ops,eval_cut) /\
    split_log_ops eval_ops flags = (raw_topics,[]) /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) /\
    compile_stmt cenv lctx ty (Log event_id args) cs = ((),cs') /\
    fn_has_code topic_cut cs' func /\ LENGTH (Lit (n2w sig_hash)::topic_ops) < dimword(:256) /\
    eval_operands (Lit (n2w sig_hash)::topic_ops) ss = SOME topics /\
    ss.vs_current_bb = topic_cut.cs_current_bb /\ ss.vs_inst_idx = LENGTH topic_cut.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      out.vs_logs = ss.vs_logs ++ [<|logger := w2w ss.vs_call_ctx.cc_address; topics := topics; data := []|>] /\
      out.vs_memory = ss.vs_memory /\
      (!arg_op. eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_state_frame ss (out with vs_logs := ss.vs_logs) /\
      copy_state_frame ss (out with vs_logs := ss.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  `emit_inst LOG (Lit (n2w (LENGTH (Lit (n2w sig_hash)::topic_ops))) ::
    REVERSE (Lit (n2w sig_hash)::topic_ops) ++ [Lit 0w;Lit 0w]) [] topic_cut = ((),cs')` by
    (drule_all_then (qspecl_then [`lctx`, `ty`] mp_tac) compile_log_stmt_empty_suffix >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `topic_cut`, `cs'`, `Lit (n2w sig_hash)::topic_ops`, `topics`,
    `Lit 0w`, `Lit 0w`, `0w`, `0w`, `ss`] emit_inst_LOG_path) >>
  impl_tac >- simp[eval_operand_def] >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `abi_state_frame ss (out with vs_logs := ss.vs_logs)` by
    (irule abi_state_frame_log_image >> qexistsl_tac [`ss`, `LENGTH cs'.cs_current_insts`] >> simp[]) >>
  `copy_state_frame ss (out with vs_logs := ss.vs_logs)` by simp[] >>
  qexists_tac `out` >> fs[read_memory_def]
QED
