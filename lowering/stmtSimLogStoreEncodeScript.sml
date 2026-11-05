(* Allocation ownership adapters for the continuing event encoder. *)
Theory stmtSimLogStoreEncode
Ancestors
  stmtSimLogStoreFresh stmtSimLogAllocate stmtSimLogEncodeFrame
  abiDecoderFrame abiBuiltinAllocation abiEncoderInput abiEncoderProps abiEncoderCounters
  localPtrsProps exprLoweringProps context compileEnv emitHelper emitHelperProps abiDecoderReentry
  venomExecSemantics venomState venomInst finite_map words list arithmetic

Theorem log_buffer_local_footprint[local]:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz [(p,cap)]
Proof
  cheat
QED

Theorem log_buffer_immutable_footprint[local]:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) ==>
  ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) [(p,cap)]
Proof
  cheat
QED

Theorem log_tuple_cursor_footprints[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w 32)] /\
  inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
  local_ptrs_reserved ce st /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srccap) /\
  FLOOKUP s.vs_allocas dstid = SOME (db,outcap) /\
  srcid <> inst.inst_id /\ dstid <> inst.inst_id /\ cap <= srccap ==>
  ?p. ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db) /\
    (!name lo sz. local_region ce es.scopes s name lo sz ==>
      abi_footprint_disjoint lo sz [(p,32)]) /\
    (ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      abi_footprint_disjoint off (type_memory_size tv) [(p,32)])
Proof
  cheat
QED

Theorem log_output_buffer_shape:
  compile_alloc_buffer cap st = (buf,prepared) ==>
  prepared.cs_next_id = st.cs_next_id + 1 /\
  prepared.cs_next_var = st.cs_next_var + 1 /\
  abi_decoder_operand_live prepared.cs_next_var buf.buf_operand
Proof
  cheat
QED

Theorem log_reserved_operand_live[local]:
  local_ptrs_reserved ce st /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
  abi_decoder_operand_live st.cs_next_var (Var v)
Proof
  cheat
QED

Theorem log_two_footprints[local]:
  abi_footprint_disjoint lo sz [a] /\ abi_footprint_disjoint lo sz [b] ==>
  abi_footprint_disjoint lo sz [a;b]
Proof
  cheat
QED

Theorem log_tuple_encoder_owned[local]:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = SOME (db,outcap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  db+outcap < dimword (:256) /\ (sb+cap <= db \/ db+outcap <= sb) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst.buf_operand initial = SOME (n2w db) /\
  abi_decoder_operand_live prepared.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual. run_inst_seq (emitted_insts prepared end_st) initial = OK actual /\
    inst_extends prepared end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live prepared.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED



Theorem log_allocated_tuple_encode_continue_bounded:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  outcap < dimword (:256) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual db. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256)
Proof
  cheat
QED

Theorem log_allocated_tuple_encode_continue:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  outcap < dimword (:256) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual db. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED
