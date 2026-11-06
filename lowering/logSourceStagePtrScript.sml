(* Allocation/staging composition protects the suffix entry state.  Transport
   back to the statement entry uses ghost_kept_wb_trans, not ghost_kept alone. *)
Theory logSourceStagePtr
Ancestors
  logSourceEntryPtr logStagedEntryPtr logTupleOwnershipPtr logGhostFramePtr
  logDataStorePtr stmtSimLogDataFrame abiBuiltinAllocation abiDecoderFrame
  exprLoweringProps bodyPtrDefs localPtrsProps compileEnv venomMemDefs
  venomState finite_map words list arithmetic appendStorageGhostPtr

Theorem log_source_allocation_regions_ptr:
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  stmt_state_rel ctx func ce cx es s /\ stmt_state_rel ctx func ce cx es t /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s t /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (b,cap) ==>
  (!name p sz. local_region ce es.scopes t name p sz ==> p+sz <= b \/ b+cap <= p) /\
  (!name p sz. local_region ce es.scopes s name p sz ==> p+sz <= b \/ b+cap <= p) /\
  (!aid p sz. FLOOKUP s.vs_allocas aid = SOME (p,sz) /\ aid < st.cs_next_id ==>
    p+sz <= b \/ b+cap <= p)
Proof
  strip_tac >>
  `!name p sz. local_region ce es.scopes t name p sz ==>
     abi_footprint_disjoint p sz [(b,cap)]` by
    (rpt gen_tac >> strip_tac >>
     irule log_buffer_registered_local_region >> metis_tac[]) >>
  conj_tac >- fs[abi_footprint_disjoint_def] >>
  conj_tac
  >- (drule_all log_allocation_local_regions >>
      fs[abi_footprint_disjoint_def] >> metis_tac[]) >>
  `t.vs_allocas = (abi_builtin_allocate_state st.cs_next_id cap s).vs_allocas` by
    fs[abi_builtin_allocation_frame_def] >>
  drule_all log_builtin_allocation_candidate >> disch_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def, state_rel_def] >>
  rpt strip_tac >>
  `aid <> st.cs_next_id` by decide_tac >>
  drule_all log_alloca_candidate_other_region >>
  simp[abi_footprint_disjoint_def] >> metis_tac[]
QED

Theorem log_allocated_source_store_path_ptr:
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  buf.buf_operand = Var src /\
  compile_log_store_data ce xs (Var src) 0 start = ((),end_st) /\
  stmt_state_rel ctx func ce cx es s0 /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  st.cs_next_var <= start.cs_next_var /\
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id cap s0 s /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,cap) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\(op,ty). !p. op = Var p ==> not_fresh_at start p) xs /\
  not_fresh_at start src /\ lookup_var src s = SOME (n2w b) /\
  ptr_covers G tn src s cap /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b+cap < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts start end_st) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d ce cx es G tn s /\ fresh_vars_wrt limit_st s /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at start p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at start p) /\
  ghost_kept ce es st G0 tn0 s0 G tn ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts start end_st))) H tm
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts start end_st))) /\
    run_inst_seq (emitted_insts start end_st) s = OK t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      log_data_layout cx (MAP SND xs) vs b m) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    ghost_inv d ce cx es H tm t /\ ghost_kept ce es st G0 tn0 s0 H tm /\
    log_write_frame start b (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
    (!p. not_fresh_at start p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p)) /\
    lookup_var src t = SOME (n2w b) /\ ptr_covers H tm src t cap /\
    t.vs_allocas = s.vs_allocas /\
    (!name p sz. local_region ce es.scopes t name p sz <=>
      local_region ce es.scopes s0 name p sz)
Proof
  strip_tac >>
  `local_ptrs_reserved ce start` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all log_source_allocation_regions_ptr >> strip_tac >>
  qpat_assum `FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,cap)`
    (mp_then (Pat `FLOOKUP _ _ = _`) mp_tac log_registered_buffer_immutable_region) >>
  disch_then drule >> disch_then drule >>
  disch_then (fn th => qpat_assum `stmt_state_rel _ _ _ _ _ s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac th)) >> disch_tac >>
  `!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) /\ aid < st.cs_next_id /\
    (!name a k. local_region ce es.scopes s0 name a k ==> p+sz <= a \/ a+k <= p) ==>
    p+sz <= b \/ b+cap <= p` by metis_tac[] >>
  `ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    p+type_memory_size tv <= b \/ b+cap <= p` by metis_tac[] >>
  drule_all compile_log_store_data_ready_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `ptr_covers H tm src t cap` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`G`,`s`,`start`,`tn`] >> simp[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (fs[log_write_frame_def, venom_state_component_equality]) >>
  `!name p sz. local_region ce es.scopes t name p sz <=>
     local_region ce es.scopes s0 name p sz` by
    (drule_all log_allocation_local_regions >> disch_tac >>
     rpt gen_tac >> drule_all log_write_frame_local_region >> metis_tac[]) >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[]
QED
