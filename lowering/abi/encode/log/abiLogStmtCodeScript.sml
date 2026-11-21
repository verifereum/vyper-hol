(* An event without data emits LOG after reading its saved topic arguments. *)
Theory abiLogStmtCode
Ancestors
  stmtLowering exprLowering compileEnv context list pair

Theorem compile_log_stmt_empty_suffix:
  !cenv lctx ty event_id args cs event_hash arg_types flags saved eval_cut raw_topics topic_ops topic_cut.
    cenv.ce_event_info (nsid_to_string event_id) = SOME (event_hash,arg_types,flags) /\
    compile_ext_call_args compile_expr cenv [] (MAP (lowered_value_type cenv) args)
      args cs = (saved,eval_cut) /\
    split_log_ops (ZIP (saved,MAP (lowered_value_type cenv) args)) flags = (raw_topics,[]) /\
    compile_log_saved_topics cenv raw_topics eval_cut = (topic_ops,topic_cut) ==>
    compile_stmt cenv lctx ty (Log event_id args) cs =
      emit_inst LOG (Lit (n2w (LENGTH (Lit (n2w event_hash)::topic_ops))) ::
        REVERSE (Lit (n2w event_hash)::topic_ops) ++ [Lit 0w;Lit 0w]) [] topic_cut
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def, LET_THM]
QED
