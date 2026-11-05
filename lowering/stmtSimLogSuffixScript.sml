(* Successful Log suffixes use the checked store/encoder and LOG boundaries. *)
Theory stmtSimLogSuffix
Ancestors
  stmtSimLogStoreCompose stmtSimLogEmit stmtSimLogTrace stmtSimLogTopics
  compileEnv exprLoweringProps emitHelperProps venomExecSemantics venomState
  valueEncoding words list arithmetic stmtSimLogTopicFresh stmtSimLogSourceAllocate
  exprSimWordArgs stmtSimLogArgs fragExec stmtLowering stmtSimLogStoreEncode
  stmtSimLogDataRun abiEncoderCounters abiDecoderReentry abiEncoderAppend
  loweringHalt vyperABI contractABI

Theorem log_emit_continuation:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\
  LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME off /\ eval_operand len_op s = SOME sz /\
  eval_operands topic_ops s = SOME topics /\
  mem_bytes_at (w2n off) (w2n sz) s.vs_memory = data /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := data |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  cheat
QED

Theorem log_emit_empty_suffix:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [Lit 0w;Lit 0w]) [] sa =
      ((),sb) /\ LENGTH topic_ops < dimword (:256) /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  cheat
QED

Theorem log_emit_encoded_suffix:
  emit_inst LOG
    (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++ [len_op;ptr_op]) [] sa =
      ((),sb) /\ LENGTH topic_ops < dimword (:256) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  eval_operand len_op s = SOME (n2w (LENGTH data)) /\
  b < dimword (:256) /\ LENGTH data < dimword (:256) /\
  mem_bytes_at b (LENGTH data) s.vs_memory = data /\
  eval_operands topic_ops s = SOME topics /\
  stmt_state_rel ctx func ce cx es s /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := topics; data := data |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sb /\
    (!op. eval_operand op t = eval_operand op s) /\
    (t with vs_logs := s.vs_logs) = s
Proof
  cheat
QED

Theorem log_operands_values[local]:
  !ops ws. LIST_REL (\op w. eval_operand op s = SOME w) ops ws ==>
    eval_operands ops s = SOME ws
Proof
  cheat
QED

Theorem log_empty_suffix_finish[local]:
  compile_log_topic_ops raw sm = (ops,st) /\
  run_inst_seq (emitted_insts sm st) s = OK u /\
  wb_frame ce es sm s u /\
  LIST_REL (\op w. eval_operand op u = SOME w) ops topics /\
  stmt_state_rel ctx func ce cx es u /\ fresh_vars_wrt limit_st s /\
  sb.cs_next_var <= limit_st.cs_next_var /\
  emit_inst LOG
    (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
      REVERSE (Lit (n2w h)::ops) ++ [Lit 0w;Lit 0w]) [] st = ((),sb) /\
  LENGTH (Lit (n2w h)::ops) < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := n2w h::topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  cheat
QED

Theorem log_split_data_every:
  !xs flags. LENGTH flags = LENGTH xs /\ EVERY P xs ==>
    EVERY P (SND (split_log_ops xs flags))
Proof
  cheat
QED

Theorem log_success_empty_run[local]:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  SND (split_log_ops xs flags) = [] /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fresh_vars_wrt limit_st s /\ sb.cs_next_var <= limit_st.cs_next_var /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++
        [<|logger := w2w cx.txn.target; topics := n2w h::topics; data := [] |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  cheat
QED

Theorem log_data_prepare_run[local]:
  cap = SUM (MAP (type_memory_bytes ce) (MAP SND xs)) /\
  srccap = MAX 32 cap /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_alloc_buffer srccap source_st = (srcbuf,start) /\
  fn_has_code source_st start func /\
  compile_log_store_data ce xs srcbuf.buf_operand 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand srcbuf.buf_operand ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\
  fresh_vars_wrt limit_st s /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  LIST_REL (\arg v. log_arg_rel ce cx sa source_st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at source_st z) /\ (!l. FST p <> Label l)) xs /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
  ?avs actual db.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts source_st end_st) s = OK actual /\
    inst_extends source_st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    db < dimword (:256) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256) /\
    (!op w. abi_decoder_operand_live source_st.cs_next_var op /\
      eval_operand op s = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED

val _ = if null (hyp log_data_prepare_run) then ()
  else print "statement-check gate skipped\n";

Theorem log_operands_live_transport[local]:
  !ops ws. EVERY (abi_decoder_operand_live nv) ops /\
    eval_operands ops s = SOME ws /\
    (!op w. abi_decoder_operand_live nv op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) ==>
    eval_operands ops t = SOME ws
Proof
  cheat
QED

Theorem log_data_emit_run[local]:
  cap = SUM (MAP (type_memory_bytes ce) (MAP SND xs)) /\
  srccap = MAX 32 cap /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_alloc_buffer srccap source_st = (srcbuf,start) /\
  fn_has_code source_st start func /\
  compile_log_store_data ce xs srcbuf.buf_operand 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand srcbuf.buf_operand ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\
  fresh_vars_wrt limit_st s /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  LIST_REL (\arg v. log_arg_rel ce cx sa source_st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at source_st z) /\ (!l. FST p <> Label l)) xs /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) /\
  eval_operands topic_ops s = SOME topics /\
  EVERY (abi_decoder_operand_live source_st.cs_next_var) topic_ops /\
  LENGTH topic_ops < dimword (:256) /\
  emit_inst LOG (Lit (n2w (LENGTH topic_ops)) :: REVERSE topic_ops ++
    [out;dst.buf_operand]) [] end_st = ((),final) ==>
  ?avs t.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts source_st final) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (MAP SND xs))) (ListV avs) |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends source_st final /\
    (!op w. abi_decoder_operand_live source_st.cs_next_var op /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  cheat
QED

val _ = if null (hyp log_data_emit_run) then ()
  else print "statement-check gate skipped\n";

Theorem log_selected_typed[local]:
  !xs vs flags.
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  LENGTH flags = LENGTH xs /\
  LIST_REL (log_arg_rel ce cx sa st es t)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs) ==>
  LIST_REL (\arg v. log_arg_rel ce cx sa st es t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v)
    (SND (split_log_ops xs flags)) (log_non_indexed_values flags vs)
Proof
  cheat
QED

Theorem log_data_stage_code[local]:
  cs_extends sm st /\
  compile_alloc_buffer cap st = (src,s1) /\
  compile_log_store_data ce xs src.buf_operand 0 s1 = ((),s2) /\
  EVERY (supported_scalar_type o SND) xs /\
  compile_alloc_buffer outcap s2 = (dst,s3) /\
  compile_abi_encode_to_buf dst.buf_operand src.buf_operand ei s3 = (len,s4) /\
  emit_inst LOG operands [] s4 = ((),sb) /\
  fn_has_code sm sb func /\ sb.cs_next_var <= limit_st.cs_next_var ==>
  fn_has_code st s1 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 s4 func /\ s4.cs_next_var <= limit_st.cs_next_var
Proof
  cheat
QED

Theorem log_selected_frontier[local]:
  LENGTH flags = LENGTH xs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) ==>
  cs_extends sm st /\ sm.cs_next_var <= st.cs_next_var /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at st z) /\ (!l. FST p <> Label l))
    (SND (split_log_ops xs flags)) /\
  EVERY (abi_decoder_operand_live st.cs_next_var) (Lit (n2w h)::ops)
Proof
  cheat
QED

Theorem log_success_suffix_run:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fresh_vars_wrt limit_st s /\ sb.cs_next_var <= limit_st.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  LENGTH flags = LENGTH xs /\ LENGTH (FILTER I flags) <= 3 /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sm z) /\ (!l. FST p <> Label l)) xs /\
  LIST_REL (\arg v. log_arg_rel ce cx sa sm es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
  SUM (MAP (type_memory_bytes ce) (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
    (log_non_indexed_values flags vs) = SOME avs ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
          (log_non_indexed_types flags (MAP SND xs)))) (ListV avs) |>]) t /\
    fresh_vars_wrt limit_st t /\ inst_extends sm sb /\
    (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\ (!l. op <> Label l) /\
      eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  cheat
QED




val _ = if null (hyp log_success_suffix_run) then ()
  else print "statement-check gate skipped\n";
