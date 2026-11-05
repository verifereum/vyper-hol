(* Compiler stage boundaries for successful event metadata lookup. *)
Theory stmtSimLogTrace
Ancestors
  stmtLowering stmtSimLogArgs stmtSimLogTopics context compileEnv emitHelper
  emitHelperProps exprLoweringProps list words abiBuiltinAllocation fragExec
  venomInst venomExecSemantics

Theorem compile_log_empty_trace:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all cenv args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (topics,st) /\
  SND (split_log_ops xs flags) = [] ==>
  (compile_stmt cenv lctx ty (Log id args) sa = ((),sb) <=>
   emit_inst LOG
     (Lit (n2w (LENGTH (Lit (n2w h)::topics))) ::
       REVERSE (Lit (n2w h)::topics) ++ [Lit 0w; Lit 0w]) [] st = ((),sb))
Proof
  strip_tac >> simp[Once compile_stmt_def, comp_bind_def, comp_return_def]
QED

Theorem compile_log_data_trace:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all cenv args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (topics,st) /\
  SND (split_log_ops xs flags) = data_ops /\ data_ops <> [] ==>
  (compile_stmt cenv lctx ty (Log id args) sa = ((),sb) <=>
   ?src s1 s2 dst s3 len s4.
     compile_alloc_buffer
       (MAX 32 (SUM (MAP (type_memory_bytes cenv) (MAP SND data_ops)))) st = (src,s1) /\
     compile_log_store_data cenv data_ops src.buf_operand 0 s1 = ((),s2) /\
     compile_alloc_buffer
       (MAX 32 (abi_size_bound cenv.ce_struct_fields (TupleT (MAP SND data_ops))))
       s2 = (dst,s3) /\
     compile_abi_encode_to_buf dst.buf_operand src.buf_operand
       (type_to_abi_enc_info cenv.ce_struct_fields cenv (TupleT (MAP SND data_ops)))
       s3 = (len,s4) /\
     emit_inst LOG
       (Lit (n2w (LENGTH (Lit (n2w h)::topics))) ::
         REVERSE (Lit (n2w h)::topics) ++ [len;dst.buf_operand]) [] s4 = ((),sb))
Proof
  strip_tac >> simp[Once compile_stmt_def, NULL_EQ, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem log_buffer_trace_code:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func ==>
  inst_extends sa sb /\ buf.buf_size = cap /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> simp[] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
        [STRING #"%" (toString sa.cs_next_var)])` by
    (`sb.cs_current_bb = sa.cs_current_bb` by gvs[inst_extends_def, same_blocks_def] >>
     drule_all fn_has_code_same_block >> simp[] >>
     disch_then (qx_choose_then `bb` strip_assume_tac) >>
     qexists_tac `bb` >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[get_instruction_def] >> metis_tac[MEM_EL]
QED
