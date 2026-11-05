(* Actual-site allocation for the two Log buffers, including re-entry. *)
Theory stmtSimLogAllocate
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogTrace stmtSimLogAllocResource stmtSimLogScalarPrefix
  abiBuiltinAllocation localPtrsProps abiEncoderComplexPrefix abiEncoderComplexCode
  abiEncoderMemberCode abiEncoderChildContext fragExec
  loweringSlice exprSimOperands  stmtSimLogArgs exprLoweringProps
  compileEnv context emitHelperProps venomExecSemantics venomInst venomState
  finite_map words list arithmetic string ASCIInumbers

Theorem log_buffer_allocate:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cap < dimword (:256) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = cap /\
    p + cap < dimword (:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,cap) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\
    abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id cap s t /\
    (!id b sz. id <> sa.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      p + cap <= b \/ b + sz <= p) /\
    inst_extends sa sb
Proof
  cheat
QED

(* Ownership follows the actual instruction site, including replayed sites. *)
Theorem log_buffer_clear_of_locals:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) /\
  local_region ce es.scopes s name lo sz ==>
  p + cap <= lo \/ lo + sz <= p
Proof
  cheat
QED

Theorem log_buffer_clear_of_immutable:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= p \/ p + cap <= off
Proof
  cheat
QED

Theorem log_pending_alloca_locals[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce es.scopes q /\
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)) /\
  local_region ce es.scopes s name lo sz ==>
  lo + sz <= p \/ p + cap <= lo
Proof
  cheat
QED

Theorem log_pending_alloca_immutable[local]:
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)) /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= p \/ p + cap <= off
Proof
  cheat
QED

(* This is the prospective cursor resource consumed by the encoder, not an
   assumption that its ALLOCA is fresh.  Its site may already be recorded. *)
Theorem log_cursor_ownership:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w 32)] /\
  inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
  local_ptrs_reserved ce st ==>
  ?p. ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\
    (!id b sz. id <> inst.inst_id /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      p+32 <= b \/ b+sz <= p) /\
    (!name lo sz. local_region ce es.scopes s name lo sz ==>
      lo+sz <= p \/ p+32 <= lo) /\
    (ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      off+type_memory_size tv <= p \/ p+32 <= off)
Proof
  cheat
QED

Theorem log_cursor_trace_code:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\
  fn_has_code st prepared func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED

Theorem log_encoder_cursor_code:
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  fn_has_code st end_st func ==>
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  cheat
QED
