(* Pointer boundary for the actual ALLOCA site of either Log buffer. *)
Theory logDataAllocPtr
Ancestors
  stmtSimLogAllocate stmtSimLogTrace abiBuiltinAllocation allocationPtr
  fragExec fragExecPtr fragGasSeqPtr logInstSeqPtr stmtLowering context compileEnv
  exprLoweringProps emitHelperProps venomInst venomExecSemantics venomState ptrDiscipline
  ptrSafeRun finite_map words list arithmetic string ASCIInumbers

Theorem log_buffer_seq_ptr:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cap < dimword (:256) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx ==>
  ?t p Gf tnf out.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
    buf.buf_operand = Var out /\ buf.buf_size = cap /\
    ptr_covers Gf tnf out t cap /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ p + cap < dimword (:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,cap) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\
    abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id cap s t /\
    (!id b sz. id <> sa.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      p + cap <= b \/ b + sz <= p) /\ inst_extends sa sb
Proof
  strip_tac >> drule_all log_buffer_allocate >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  qexistsl_tac [`t`, `p`,
    `step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
       [STRING #"%" (toString sa.cs_next_var)]) t`,
    `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)]
       [STRING #"%" (toString sa.cs_next_var)]) s t tn`,
    `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[] >> conj_tac >- suspend "check" >>
  reverse conj_tac >- metis_tac[ADD_COMM] >>
  irule alloca_step_ptr_covers >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED
Resume log_buffer_seq_ptr[check]:
  simp[inst_seq_ptr_def] >>
  irule ptr_inst_ok_alloca >> simp[]
QED
Finalise log_buffer_seq_ptr

Theorem log_buffer_path_ptr:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ cap < dimword (:256) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t p Gf tnf out.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf
      (OK (t with vs_inst_idx := s.vs_inst_idx + 1)) /\
    buf.buf_operand = Var out /\ buf.buf_size = cap /\
    ptr_covers Gf tnf out (t with vs_inst_idx := s.vs_inst_idx + 1) cap /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ p + cap < dimword (:256) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,cap) /\
    stmt_state_rel ctx func ce cx es (t with vs_inst_idx := s.vs_inst_idx + 1) /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\
    abi_builtin_allocation_frame sa.cs_next_var sa.cs_next_id cap s t /\
    (!id b sz. id <> sa.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
      p + cap <= b \/ b + sz <= p) /\ inst_extends sa sb
Proof
  strip_tac >> drule_all log_buffer_seq_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`t`, `p`, `Gf`, `tnf`, `out`] >>
  gvs[mk_inst_def, stmt_state_rel_inst_idx] >> metis_tac[ADD_COMM]
QED
