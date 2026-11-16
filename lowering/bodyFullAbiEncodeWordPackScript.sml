Theory bodyFullAbiEncodeWordPack
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeFinish exprSimAbiEncodeStagedObserver
  exprSimAbiEncodeStateTransport exprSimAbiEncodeOblivious
  abiBuiltinEncodeCode abiEncoderAppend loweringHalt exprSimHash
  emitHelper emitHelperProps exprLoweringProps localPtrsProps freshWrites
  fragExec compileEnv venomState venomExecSemantics venomInst finite_map words arithmetic
  pred_set list rich_list

Theorem abi_encode_word_pack_origin:
  lower_abi_encode F mid (Var src) (AbiCopy 32) 32 st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved ce st /\ local_ptrs_reserved ce origin /\ cs_extends origin st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st x) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  source_id < st.cs_next_id /\ FLOOKUP s.vs_allocas source_id = SOME (sb,32) /\
  eval_operand (Var src) s = SOME (n2w sb) /\ ptr_covers G tn src s 32 /\
  not_fresh_at st src /\ abi_encoder_admissible (AbiCopy 32) /\
  LENGTH (enc at av) = 32 /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiCopy 32) at av sb 32 mem) /\
  stmt_state_rel (Hentry:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ wb_frame ce es ee origin s0 s /\
  ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
  let k = (case mid of NONE => 0 | SOME _ => 4) in
  let N = 32+32*word_size (32+k) in
  ?p q t Gt tnt.
    out = Var q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tnt)) /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\
    eval_operand out t = SOME (n2w p) /\ ptr_covers Gt tnt q t N /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,N) /\
    p+N <= t.vs_alloca_next /\ t.vs_alloca_next < dimword(:256) /\
    (!mem. mem_agree_outside tnt.t_mem t.vs_memory mem ==>
      mem_word_at p mem = n2w (32+k) /\
      mem_bytes_at (p+32+k) 32 mem = enc at av /\
      (case mid of NONE => T | SOME selector =>
        mem_bytes_at (p+32) 4 mem = abi_builtin_encode_method_bytes selector)) /\
    alloca_history func t /\ allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!H. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s ==>
      abi_encode_staged_observation H ctx func ce cx ee st out mid N p at av s t) /\
    (!H D. stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
      ghost_inv_at D lo ret ce cx ee G tn s ==> ghost_inv_at D lo ret ce cx ee Gt tnt t) /\
    ghost_kept_at lo ce es origin G0 tn0 s0 Gt tnt /\ wb_frame ce es ee origin s0 t /\
    (pure_frame ce func es origin s0 s ==> pure_frame ce func es origin s0 t)
Proof
  strip_tac >> pure_rewrite_tac [LET_THM] >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_trace >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ st = (buf,allocated)` >>
  `cs_extends st allocated /\ cs_extends allocated address_st /\
   cs_extends address_st ready /\ cs_extends ready body_end /\ cs_extends body_end final` by
    (conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     conj_tac >- metis_tac[emit_op_extends, same_blocks_def, cs_extends_same_block, IS_PREFIX_APPEND] >>
     conj_tac >- (Cases_on `mid`
       >- gvs[abi_builtin_encode_method_id_def, comp_return_def, cs_extends_refl] >>
       qpat_x_assum `abi_builtin_encode_method_id _ _ _ = _` mp_tac >>
       simp[NoAsms, abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
         emit_def] >> strip_tac >> gvs[] >>
       simp[cs_extends_def, IS_PREFIX_APPEND]) >>
     conj_tac >- metis_tac[compile_abi_encode_to_buf_extends] >>
     qpat_x_assum `abi_builtin_encode_finish _ _ _ _ = _` mp_tac >>
     simp[NoAsms, abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def] >> IF_CASES_TAC >> strip_tac >> gvs[] >>
     simp[cs_extends_def, IS_PREFIX_APPEND]) >>
  `fn_has_code st allocated func /\ fn_has_code allocated ready func /\
   fn_has_code ready body_end func /\ fn_has_code body_end final func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_encode_alloc_origin_exact >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`,`tn`] mp_tac) >>
  FAIL_TAC "allocation interface"
QED
