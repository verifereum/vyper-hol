(* Captured argument ownership across the first actual-site Log allocation. *)
Theory stmtSimLogSourceAllocate
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogAllocate stmtSimLogDataFrame stmtSimLogDataRun stmtSimLogArgs
  abiBuiltinAllocation abiDecoderReentry exprSimWordArgs 
  exprLoweringProps compileEnv venomState venomMemDefs valueTypingMemoryProps
  valueEncoding supportedTypes finite_map words list arithmetic emitHelperProps ASCIInumbers

Theorem log_allocation_wb_frame[local]:
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t ==>
  wb_frame ce es st s t
Proof
  cheat
QED

Theorem log_allocated_arg[local]:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t /\
  (!z. FST arg = Var z ==> not_fresh_at st z) /\ (!l. FST arg <> Label l) /\
  supported_scalar_type (SND arg) /\ log_arg_rel ce cx sa st es s arg v ==>
  log_arg_rel ce cx sa st es t arg v
Proof
  cheat
QED

Theorem log_allocated_data_sources[local]:
  !xs vs.
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  stmt_state_rel ctx func ce cx es s /\ stmt_state_rel ctx func ce cx es t /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,cap) /\
  LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at st z) /\ (!l. FST p <> Label l)) xs ==>
  LIST_REL (log_data_source cx b cap t) xs vs
Proof
  cheat
QED

Theorem log_buffer_allocate_sources:
  compile_alloc_buffer cap source_st = (buf,start) /\
  fn_has_code source_st start func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce source_st /\ cap < dimword (:256) /\
  start.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  LIST_REL (\arg v. log_arg_rel ce cx sa source_st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs /\
  EVERY (\p. (!z. FST p = Var z ==> not_fresh_at source_st z) /\
    (!l. FST p <> Label l)) xs ==>
  ?t p. run_inst_seq (emitted_insts source_st start) s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = cap /\
    p + cap < dimword (:256) /\
    FLOOKUP t.vs_allocas source_st.cs_next_id = SOME (p,cap) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live source_st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\
    abi_builtin_allocation_frame source_st.cs_next_var source_st.cs_next_id cap s t /\
    (!id b sz. id <> source_st.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      p + cap <= b \/ b + sz <= p) /\
    inst_extends source_st start /\
    LIST_REL (log_data_source cx p cap t) xs vs /\
    source_st.cs_next_id < start.cs_next_id /\
    abi_decoder_operand_live start.cs_next_var buf.buf_operand /\
    EVERY (\(op,ty). !z. op = Var z ==> not_fresh_at start z) xs
Proof
  cheat
QED
