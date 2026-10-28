(* TOP-LEVEL: connect the verified encoder/emitter suffix to actual Log
   statement lowering after argument evaluation, topics, and data storage. *)
Theory abiLogStmtCode
Ancestors
  abiLogCode stmtLowering compileEnv context list pair

Theorem compile_log_stmt_nonempty_suffix:
  !cenv lctx ty event_id args cs event_hash arg_types flags eval_ops eval_cut
    raw_topics data_ops topic_ops topic_cut data_types data_alloc store_cut
    alloc_cut abi_alloc encode_cut.
    cenv.ce_event_info (nsid_to_string event_id) = SOME (event_hash,arg_types,flags) /\
    compile_log_eval_all cenv args cs = (eval_ops,eval_cut) /\
    split_log_ops eval_ops flags = (raw_topics,data_ops) /\ ~NULL data_ops /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) /\
    data_types = log_non_indexed_types flags arg_types /\
    compile_alloc_buffer (MAX 32 (SUM (MAP (type_memory_bytes cenv) data_types))) topic_cut = (data_alloc,store_cut) /\
    compile_log_store_data cenv data_ops data_types data_alloc.buf_operand 0 store_cut = ((),alloc_cut) /\
    compile_alloc_buffer (MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT data_types))) alloc_cut = (abi_alloc,encode_cut) ==>
    compile_stmt cenv lctx ty (Log event_id args) cs =
      compile_log_abi_emit abi_alloc.buf_operand data_alloc.buf_operand
        (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT data_types))
        (Lit (n2w event_hash)::topic_ops) encode_cut
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def, LET_THM, compile_log_abi_emit_def]
QED

Theorem compile_log_stmt_empty_suffix:
  !cenv lctx ty event_id args cs event_hash arg_types flags eval_ops eval_cut raw_topics topic_ops topic_cut.
    cenv.ce_event_info (nsid_to_string event_id) = SOME (event_hash,arg_types,flags) /\
    compile_log_eval_all cenv args cs = (eval_ops,eval_cut) /\
    split_log_ops eval_ops flags = (raw_topics,[]) /\
    compile_log_topic_ops raw_topics eval_cut = (topic_ops,topic_cut) ==>
    compile_stmt cenv lctx ty (Log event_id args) cs =
      emit_inst LOG (Lit (n2w (LENGTH (Lit (n2w event_hash)::topic_ops))) ::
        REVERSE (Lit (n2w event_hash)::topic_ops) ++ [Lit 0w;Lit 0w]) [] topic_cut
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def, LET_THM]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual Log statement suffix connection: " ^ name)
  end) (DB.thms "abiLogStmtCode")
