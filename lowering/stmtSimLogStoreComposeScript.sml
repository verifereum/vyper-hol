Theory stmtSimLogStoreCompose
Ancestors
  stmtSimLogStoreEncode stmtSimLogStoreContinue stmtSimLogStoreFresh
  stmtSimLogEncodeLayout stmtSimLogDataInput vyperTypeABI vyperABI compileEnv supportedTypes contractABI list stmtSimLogAllocate abiDecoderReentry exprLoweringProps vyperTyping abiEncoderCounters stmtSimLogTrace emitHelperProps stmtSimLogDataRun arithmetic words

val _ = if null (hyp stmtSimLogStoreContinueTheory.log_store_data_stmt)
  then print "STORE PREREQUISITE CLOSED\n"
  else (print_thm stmtSimLogStoreContinueTheory.log_store_data_stmt;
        print "statement-check gate skipped\n");

Theorem log_scalar_embedded_bound[local]:
  supported_scalar_type ty ==>
  vyper_abi_embedded_size env ty =
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)
Proof
  cheat
QED

Theorem log_tuple_source_bound[local]:
  !tys. EVERY supported_scalar_type tys ==>
  vyper_abi_size_bound_list env tys = abi_size_bound ce.ce_struct_fields (TupleT tys)
Proof
  cheat
QED

Theorem log_stored_tuple_encoding_bound[local]:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  vyper_to_abi_list (get_tenv cx) tys vs = SOME avs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) tys)) (ListV avs)) <=
    abi_size_bound ce.ce_struct_fields (TupleT tys)
Proof
  cheat
QED

Theorem log_tuple_encoder_shape[local]:
  EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ((?n. type_to_abi_enc_info sf ce (TupleT tys) = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. type_to_abi_enc_info sf ce (TupleT tys) = AbiComplex infos /\
    EXISTS (\(_,_,_,dyn). dyn) infos /\
    EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))
Proof
  cheat
QED

Theorem log_store_encode_continue_bounded:
  cap = SUM (MAP (type_memory_bytes ce) (MAP SND xs)) /\
  srccap = MAX 32 cap /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_alloc_buffer srccap source_st = (srcbuf,source_end) /\
  fn_has_code source_st source_end func /\
  FLOOKUP initial.vs_allocas source_st.cs_next_id = SOME (b,srccap) /\
  source_st.cs_next_id < start.cs_next_id /\ b+srccap < dimword (:256) /\
  eval_operand src initial = SOME (n2w b) /\
  LIST_REL (log_data_source cx b srccap initial) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at start x) xs /\
  abi_decoder_operand_live start.cs_next_var src /\
  compile_log_store_data ce xs src 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\ local_ptrs_reserved ce start /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
  ?avs actual db.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts start end_st) initial = OK actual /\
    inst_extends start end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256) /\
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) < dimword (:256)
Proof
  cheat
QED




Theorem log_store_encode_continue:
  cap = SUM (MAP (type_memory_bytes ce) (MAP SND xs)) /\
  srccap = MAX 32 cap /\
  outcap = MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs))) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)) /\
  compile_alloc_buffer srccap source_st = (srcbuf,source_end) /\
  fn_has_code source_st source_end func /\
  FLOOKUP initial.vs_allocas source_st.cs_next_id = SOME (b,srccap) /\
  source_st.cs_next_id < start.cs_next_id /\ b+srccap < dimword (:256) /\
  eval_operand src initial = SOME (n2w b) /\
  LIST_REL (log_data_source cx b srccap initial) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at start x) xs /\
  abi_decoder_operand_live start.cs_next_var src /\
  compile_log_store_data ce xs src 0 start = ((),stored_st) /\
  compile_alloc_buffer outcap stored_st = (dst,prepared) /\
  fn_has_code stored_st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\ local_ptrs_reserved ce start /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  EVERY supported_scalar_type (MAP SND xs) /\ cap < dimword (:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) < dimword (:256) ==>
  ?avs actual db.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    run_inst_seq (emitted_insts start end_st) initial = OK actual /\
    inst_extends start end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs))) actual.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED

val _ = app (fn (name,th) => if null (hyp th) then ()
  else (app (fn tm => (print_term tm; print "\n")) (hyp th);
        print "statement-check gate skipped\n"))
  [("log_store_encode_continue_bounded",log_store_encode_continue_bounded),
   ("log_store_encode_continue",log_store_encode_continue)];
