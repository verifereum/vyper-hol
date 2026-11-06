(* Counted source allocation followed by robust data staging. *)
Theory logSourceStoreRunPtr
Ancestors
  logSourceStagePtr logDataAllocPtr fragGasSeqPtr entrySinkExtraction
  logSourceEntryPtr logDataStorePtr emitHelper stmtFragPtr ghostPcTransportPtr exprSimPtrLiteralBuffer
  exprLoweringProps abiBuiltinAllocation emitHelperProps bodyPtrDefs
  compileEnv stmtSimLogDataFrame abiDecoderReentry abiDecoderFrame fragGasPathPtr
  stmtSimLogSuffixFrame
  venomState venomInst finite_map words list arithmetic

Theorem log_source_store_run_path_ptr:
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  compile_log_store_data ce xs buf.buf_operand 0 start = ((),end_st) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ cap < dimword(:256) /\
  start.cs_next_var <= end_st.cs_next_var /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\ ghost_inv d ce cx es G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\arg. (!x. FST arg = Var x ==> not_fresh_at st x) /\
    (!l. FST arg <> Label l)) xs /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st start) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts start end_st)
    (DROP (s.vs_inst_idx + LENGTH (emitted_insts st start)) bb.bb_instructions) ==>
  ?H tm t b src.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st start)) +
       LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts start end_st))) H tm
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st start) +
        LENGTH (emitted_insts start end_st))) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      log_data_layout cx (MAP SND xs) vs b m) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    ghost_inv d ce cx es H tm t /\ ghost_kept ce es st G tn s H tm /\
    buf.buf_operand = Var src /\ buf.buf_size = cap /\
    lookup_var src t = SOME (n2w b) /\ ptr_covers H tm src t cap /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,cap) /\ b+cap < dimword(:256) /\
    st.cs_next_id < start.cs_next_id /\ inst_extends st start /\
    (!name p sz. local_region ce es.scopes t name p sz <=>
      local_region ce es.scopes s name p sz) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    (!p. not_fresh_at st p ==> op_taint tm (Var p) = op_taint tn (Var p)) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `start.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_buffer_allocate_sources_seq_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts st start) s = OK u` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st start)` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
  `!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP u.vs_allocas aid = SOME a` by
    (match_mp_tac log_run_old_allocas >>
     qexists_tac `emitted_insts st start` >> simp[] >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_ptr >> disch_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `st.cs_next_var <= start.cs_next_var` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> simp[]) >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at start p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at start p)` by
    metis_tac[not_fresh_at_mono] >>
  gvs[] >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule log_allocated_source_store_path_ptr >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (fn th => qpat_assum `buf.buf_operand = Var out`
    (fn eq => drule_all (SRULE [eq] th))) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> disch_tac >>
  `!p. not_fresh_at st p ==> not_fresh_at start p` by
    metis_tac[not_fresh_at_mono] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `eval_operand op t = eval_operand op u` by
       (irule log_write_frame_operand >> goal_assum (drule_at Any) >>
        rpt strip_tac >> gvs[abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    fs[log_write_frame_def, venom_state_component_equality] >>
  qexistsl_tac [`H'`,`tm'`,`t`,`b`] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ H' tm' _` mp_tac >>
      simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED
