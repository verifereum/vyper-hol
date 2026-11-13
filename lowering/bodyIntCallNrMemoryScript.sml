Theory bodyIntCallNrMemory
Ancestors
  bodyIntCallAssemblyFrame bodyIntCallCompletedModes compileEnv
  emitHelper emitHelperProps intCallFrame venomExecSemantics venomState
  fragGasPath fragGasFocus loweringPosts loweringStateRelDefs vyperTyping
  valueTypingMemoryProps valueEncodingProofs exprSimProps

Theorem nr_memory_physical_endpoint:
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  compile_alloc_buffer bsz st1 = (buf,st2) /\
  st2.cs_next_var <= si.cs_next_var /\
  value_has_type tv v /\ type_memory_size tv <= buf.buf_size /\
  eval_operand buf.buf_operand t = SOME (n2w off) /\
  FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_in_memory tv v off cs.vs_memory /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  wb_frame ce es0 es sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce es.scopes t id b sz) /\
  (!id b sz aid off asz.
    local_region ce es.scopes t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  ?out. gas_path ctx func t n (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with scopes := es.scopes) out /\
    wb_frame ce es0 (ee with scopes := es.scopes) sa s0 out /\
    eval_operand buf.buf_operand out = SOME (n2w off) /\
    val_in_memory tv v off out.vs_memory /\
    FLOOKUP out.vs_allocas aid = SOME (off,buf.buf_size) /\
    val_footprint tv v <= buf.buf_size /\
    (!id lb lsz. local_region ce es.scopes out id lb lsz ==>
      off + buf.buf_size <= lb \/ lb + lsz <= off)
Proof
  strip_tac >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  drule_all (SRULE [] (Q.INST [`outs` |-> `[]`] return_successor_frame)) >>
  strip_tac >> drule_all void_outputs_counted_path >> strip_tac >>
  `val_footprint tv v <= buf.buf_size` by
    (drule value_has_type_memory_wf >> strip_tac >>
     drule val_footprint_le >> simp[]) >>
  `sb.cs_current_bb = si.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH si.cs_current_insts)` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all compiled_return_buffer_geometry >> strip_tac >>
  qexists_tac `merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx` >>
  simp[merge_callee_state_def, eval_operand_def, lookup_var_def] >>
  conj_tac >- gvs[eval_operand_def, lookup_var_def] >>
  rpt strip_tac >>
  qpat_x_assum `!id b sz aid off asz. _` drule >>
  simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
