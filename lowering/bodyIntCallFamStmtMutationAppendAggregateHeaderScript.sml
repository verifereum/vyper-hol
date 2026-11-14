(* Header write after copying: generated registers may already be bound. *)
Theory bodyIntCallFamStmtMutationAppendAggregateHeader
Ancestors
  bodyIntCallFamStmtMutationAppendAggregatePost
  stmtSimAppendStorage appendStorageRel compileEnv exprLoweringProps
  emitHelper emitHelperProps venomState venomInst venomExecSemantics stateFrame
  loweringStateRelDefs stmtReasonLitFragMemory exprSimHashBoundary
  fragGasPath words

Theorem intcall_append_header_add_run[local]:
  emit_op ADD [lop;Lit 1w] sa = (nop,sm) /\
  eval_operand lop s = SOME len ==>
  run_inst_seq (emitted_insts sa sm) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (len+1w) s) /\
  nop = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `eval_operand (Lit 1w) s = SOME 1w` by simp[eval_operand_def] >>
  simp[run_inst_seq_def,stmtReasonMemoryTheory.step_add_eq]
QED

Theorem intcall_append_header_store_run[local]:
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] sm = ((),sb) /\
  eval_operand bop u = SOME slot /\ eval_operand nop u = SOME value /\
  ~u.vs_call_ctx.cc_static ==>
  run_inst_seq (emitted_insts sm sb) u =
    OK (if tr then tstore slot value u else sstore slot value u)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  Cases_on `tr` >> gvs[run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs,mk_inst_def,exec_write2_def]
QED

Theorem intcall_append_aggregate_header_old_landing:
  emit_op ADD [lop;Lit 1w] sa = (nop,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;nop] sm = ((),sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  local_ptrs_reserved ce sa /\
  (!x. lop = Var x \/ bop = Var x ==> not_fresh_at sa x) /\
  eval_operand lop s = SOME len /\ eval_operand bop s = SOME slot /\
  stmt_state_rel ctx func ce cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx
      (set_storage cx es tr (update_storage slot (len+1w) (get_storage cx es tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all intcall_append_header_add_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK u` >>
  `eval_operand bop u = SOME slot /\ eval_operand nop u = SOME (len+1w) /\
   ~u.vs_call_ctx.cc_static` by
    (Cases_on `bop` >>
     gvs[Abbr `u`,eval_operand_def,lookup_var_def,update_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all intcall_append_header_store_run >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (simp[Abbr `u`] >> irule stmt_state_rel_update_var >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists `sa` >> simp[]) >>
  drule_all intcall_append_header_state >>
  disch_then (qspec_then `len+1w` assume_tac) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (if tr then tstore slot (len+1w) u else sstore slot (len+1w) u)` by
    (irule run_inst_seq_compose_ok >> qexistsl [`u`,`sm`] >> simp[]) >>
  `same_blocks sa sb` by
    (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     metis_tac[same_blocks_trans]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     Cases_on `tr` >>
     simp[emit_op_def,emit_void_def,fresh_id_def,fresh_var_def,emit_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def] >>
     once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp[rich_listTheory.DROP_APPEND2,mk_inst_def,is_terminator_def]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[listTheory.FILTER_EQ_NIL] >> fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all hash_run_path >> strip_tac >>
  qexists `(if tr then tstore slot (len+1w) u else sstore slot (len+1w) u)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_inst_idx,state_frame_def,same_blocks_def,sstore_def,tstore_def,
      Abbr `u`,update_var_def,lookup_var_def,finite_mapTheory.FLOOKUP_UPDATE] >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED
