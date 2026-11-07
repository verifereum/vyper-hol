(* Source allocation preserves captured scalar arguments, including robust
   pointer values; allocation may reuse a site, so semantic ownership matters. *)
Theory logSourceEntryPtr
Ancestors
  logAllocFramePtr logStagedEntryPtr logTupleOwnershipPtr
  stmtSimLogSourceAllocate stmtSimLogArgs stmtSimLogDataRun
  abiBuiltinAllocation emitHelperProps exprLoweringProps bodyPtrDefs
  venomInst words list arithmetic fragGasSeqPtr compileEnv logDataAllocPtr
  venomState venomInstProps abiDecoderReentry

Theorem log_buffer_data_values_seq_ptr:
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  run_inst_seq (emitted_insts st start) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st start) s H tm /\
  stmt_state_rel ctx func ce cx es s /\ cap < dimword(:256) /\
  LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\arg. !x. FST arg = Var x ==> not_fresh_at st x) xs ==>
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op H tm t) xs vs
Proof
  strip_tac >> drule_all log_buffer_alloca_step >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `EVERY _ xs` mp_tac >>
  qpat_x_assum `LIST_REL (\(op,ty) v. _) xs vs` mp_tac >>
  qpat_x_assum `LIST_REL _ xs vs` mp_tac >>
  qid_spec_tac `vs` >> Induct_on `xs` >- simp[] >>
  Cases_on `vs` >- simp[] >> qx_gen_tac `arg` >> PairCases_on `arg` >>
  simp[] >> rpt strip_tac
  >- (irule alloca_step_ptr_val_ok >> simp[] >>
      reverse conj_tac
      >- (qexistsl_tac [`ce`,`ctx`,`es`,`func`,`sa`,`st`] >>
          fs[log_arg_rel_def]) >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!x. arg0 = Var x ==> _` drule >>
      simp[not_fresh_at_def]) >>
  first_x_assum irule >> simp[]
QED

Theorem log_buffer_allocate_sources_seq_ptr:
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ cap < dimword(:256) /\
  start.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\ ghost_inv d ce cx es G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\arg. (!x. FST arg = Var x ==> not_fresh_at st x) /\
    (!l. FST arg <> Label l)) xs ==>
  ?t b H tm out.
    run_inst_seq (emitted_insts st start) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st start) s H tm /\
    buf.buf_operand = Var out /\ buf.buf_size = cap /\
    ptr_covers H tm out t cap /\ lookup_var out t = SOME (n2w b) /\
    b+cap < dimword(:256) /\ FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,cap) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op H tm t) xs vs /\
    ghost_inv d ce cx es H tm t /\ ghost_kept ce es st G tn s H tm /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    (!p. not_fresh_at st p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p)) /\
    t.vs_memory = s.vs_memory /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t /\
    (!id p sz. id <> st.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,sz) ==>
      b+cap <= p \/ p+sz <= b) /\
    inst_extends st start /\ st.cs_next_id < start.cs_next_id /\
    not_fresh_at start out /\
    EVERY (\(op,ty). !p. op = Var p ==> not_fresh_at start p) xs
Proof
  strip_tac >>
  `LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
     supported_scalar_type (SND arg) /\
     ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs` by
    (qpat_x_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ arg v /\ _) xs vs` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[] >> metis_tac[]) >>
  drule_all log_buffer_allocate_sources >> strip_tac >>
  qpat_x_assum `stmt_state_rel ctx func ce cx es t` kall_tac >>
  drule_all log_buffer_seq_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  gvs[] >>
  `EVERY (\arg. !x. FST arg = Var x ==> not_fresh_at st x) xs` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `buf.buf_size < dimword(:256)` by decide_tac >>
  drule_all log_buffer_data_values_seq_ptr >> disch_tac >>
  drule_all log_buffer_ghost_seq_ptr >> disch_then (qspec_then `t.vs_inst_idx` strip_assume_tac) >>
  `!p. not_fresh_at st p ==> FLOOKUP Gf p = FLOOKUP G p /\
     op_taint tnf (Var p) = op_taint tn (Var p)` by
    (match_mp_tac (Q.INST [`cap` |-> `buf.buf_size`, `sb` |-> `start`]
       log_buffer_old_ghost_seq_ptr) >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`Gf`,`tnf`] >>
  gvs[eval_operand_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    not_fresh_at_def, venom_state_component_equality] >>
  metis_tac[]
QED
