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
  cheat
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
  cheat
QED

Theorem log_buffer_trace_code:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func ==>
  inst_extends sa sb /\ buf.buf_size = cap /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED
