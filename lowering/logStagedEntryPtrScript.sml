(* Ghost transport for staging is separate from the counted store path:
   only the newly allocated source region may change. *)
Theory logStagedEntryPtr
Ancestors
  logDataStorePtr logEncoderEntryPtr stmtSimLogStoreContinue stmtSimLogDataRun
  stmtSimLogStoreFresh stmtSimLogDataInput bodyPtrDefs stmtFragPtr
  exprSimDefs compileEnv loweringStateRelDefs localPtrsProps exprLoweringProps stmtSimLogTrace
  abiBuiltinAllocation emitHelperProps venomInst words list arithmetic

Theorem log_staged_entry_state_ptr:
  compile_log_store_data ce xs (Var buf) off sa = ((),sb) /\
  EVERY (supported_scalar_type o SND) xs /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  log_write_frame sa (b+off)
    (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fresh_vars_wrt limit_st s /\ sb.cs_next_var <= limit_st.cs_next_var /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
    lo+sz <= b+off \/ b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= lo) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    p+type_memory_size tv <= b+off \/
    b+off+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= p) ==>
  stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t
Proof
  strip_tac >>
  drule_all log_store_data_memory_mono >> disch_tac >>
  conj_tac
  >- (irule log_write_frame_stmt >> qexistsl_tac [`b+off`,`SUM (MAP (type_memory_bytes ce) (MAP SND xs))`,`s`,`sa`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  drule_all log_store_data_fresh >> simp[]
QED

Theorem log_registered_buffer_immutable_region:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,cap) ==>
  ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    off+type_memory_size tv <= b \/ b+cap <= off
Proof
  strip_tac >> drule_all log_buffer_trace_code >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  fs[stmt_state_rel_def, immutable_alloca_sep_def] >> rpt strip_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` drule >>
  disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `!inst b sz. _` drule >>
  simp[mk_inst_def, loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem compile_log_store_data_ready_path_ptr:
  compile_log_store_data ce xs (Var buf) 0 sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  not_fresh_at sa buf /\ lookup_var buf s = SOME (n2w b) /\
  ptr_covers G tn buf s cap /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  b+cap < dimword(:256) /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\ fresh_vars_wrt limit_st s /\
  sb.cs_next_var <= limit_st.cs_next_var /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!name p sz. local_region ce es.scopes s name p sz ==> p+sz <= b \/ b+cap <= p) /\
  (ce.ce_is_ctor ==> !name tv v p.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    p+type_memory_size tv <= b \/ b+cap <= p) /\
  ghost_kept ce es se G0 tn0 s0 G tn /\ se.cs_next_var <= sa.cs_next_var /\
  (!aid p sz. FLOOKUP s0.vs_allocas aid = SOME (p,sz) /\ aid < se.cs_next_id /\
    (!name a k. local_region ce es.scopes s0 name a k ==> p+sz <= a \/ a+k <= p) ==>
    p+sz <= b \/ b+cap <= p) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==> p+sz <= b \/ b+cap <= p) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb))) H tm
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      log_data_layout cx (MAP SND xs) vs b m) /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    ghost_inv d ce cx es H tm t /\ ghost_kept ce es se G0 tn0 s0 H tm /\
    log_write_frame sa b (SUM (MAP (type_memory_bytes ce) (MAP SND xs))) s t /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.INST [`off` |-> `0`] compile_log_store_data_path_ptr)) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `EVERY (supported_scalar_type o SND) xs` by metis_tac[log_data_sources_types] >>
  `local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `!name p sz. local_region ce es.scopes s name p sz ==>
     p+sz <= b \/ b+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= p` by
    (rpt strip_tac >> res_tac >> decide_tac) >>
  `ce.ce_is_ctor ==> !name tv v p.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc p) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
     p+type_memory_size tv <= b \/ b+SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= p` by
    (rpt strip_tac >> res_tac >> decide_tac) >>
  drule_all (SRULE [] (Q.INST [`off` |-> `0`] log_staged_entry_state_ptr)) >> strip_tac >>
  drule_all (SRULE [] log_data_write_ghost_inv) >> disch_tac >>
  `ghost_kept ce es se G0 tn0 s0 H tm` by
    (irule log_data_write_ghost_kept >>
     qexistsl_tac [`G`,`b`,`cap`,`sa`,`tn`] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!p. not_fresh_at sa p ==> _` drule >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!i. _ ==> mem_bytes_at _ _ _ = _ /\ _` (qspec_then `i` mp_tac) >>
       impl_tac >- decide_tac >> simp[]) >>
     simp[]) >>
  qexistsl_tac [`H`,`tm`,`t`] >> fs[]
QED
