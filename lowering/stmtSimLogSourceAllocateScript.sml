(* Captured argument ownership across the first actual-site Log allocation. *)
Theory stmtSimLogSourceAllocate
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogAllocate stmtSimLogDataFrame stmtSimLogDataRun stmtSimLogArgs
  abiBuiltinAllocation abiDecoderReentry exprSimWordArgs 
  exprLoweringProps compileEnv loweringStateRelDefs venomState venomMemDefs valueTypingMemoryProps
  valueEncoding supportedTypes finite_map words list arithmetic emitHelperProps ASCIInumbers

Theorem log_allocation_wb_frame[local]:
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t ==>
  wb_frame ce es st s t
Proof
  simp[abi_builtin_allocation_frame_def, wb_frame_def, locals_kept_def] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live st.cs_next_var (Var x)` by
        gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
            not_fresh_at_def] >>
      `eval_operand (Var x) s = SOME w` by simp[eval_operand_def] >>
      first_x_assum drule_all >> simp[eval_operand_def]) >>
  rpt strip_tac >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id = NONE` >> gvs[FLOOKUP_UPDATE] >>
  Cases_on `aid = st.cs_next_id` >> gvs[]
QED

Theorem log_allocated_arg[local]:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t /\
  (!z. FST arg = Var z ==> not_fresh_at st z) /\ (!l. FST arg <> Label l) /\
  supported_scalar_type (SND arg) /\ log_arg_rel ce cx sa st es s arg v ==>
  log_arg_rel ce cx sa st es t arg v
Proof
  strip_tac >> drule log_allocation_wb_frame >> strip_tac >>
  irule log_arg_rel_frame >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
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
  Induct_on `xs` >- simp[] >>
  gen_tac >> PairCases_on `h` >> Cases_on `vs` >> simp[] >>
  rpt strip_tac
  >- (`log_arg_rel ce cx sa st es t (h0,h1) h` by
        (irule log_allocated_arg >> simp[] >>
         qexistsl_tac [`cap`,`ctx`,`func`,`s`] >> simp[]) >>
      `expr_val_at ce cx h1 sa st es h h0 t` by gvs[log_arg_rel_def] >>
      `allocas_non_overlapping t` by gvs[stmt_state_rel_def, alloca_inv_def] >>
      `!name a k. local_region ce es.scopes t name a k ==>
         a+k <= b \/ b+cap <= a` by
        (rpt strip_tac >> drule_all log_buffer_clear_of_locals >> decide_tac) >>
      `log_source_apart cx b cap (h0,h1) h t` by
        (irule log_allocated_source_apart >> simp[] >>
         qexistsl_tac [`ce`,`st.cs_next_id`,`es`,`sa`,`st`] >> simp[] >>
         first_assum ACCEPT_TAC) >>
      simp[log_data_source_def] >> conj_tac
      >- (irule value_has_type_memory_wf >> simp[]) >>
      gvs[log_arg_rel_def]) >>
  first_x_assum drule_all >> simp[]
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
  strip_tac >> drule_all log_buffer_allocate >> strip_tac >>
  `LIST_REL (log_data_source cx p cap t) xs vs` by
    (irule log_allocated_data_sources >> simp[] >>
     qexistsl_tac [`buf`,`ce`,`ctx`,`es`,`func`,`s`,`sa`,`source_st`,`start`] >> simp[]) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [`t`,`p`] >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, toString_inj] >>
  qpat_x_assum `EVERY _ xs` mp_tac >>
  match_mp_tac listTheory.EVERY_MONOTONIC >>
  PairCases >> simp[not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED
