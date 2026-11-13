Theory bodyIntCallNrVoid
Ancestors
  bodyIntCallAssemblyFrame bodyIntCallCompletedModes compileEnv
  emitHelper emitHelperProps intCallFrame venomExecSemantics venomState
  fragGasPath fragGasFocus loweringPosts loweringStateRelDefs vyperTyping

Theorem nr_void_physical_endpoint:
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  value_has_type NoneTV v /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  wb_frame ce es0 es sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce es.scopes t id b sz) /\
  (!id b sz aid off asz.
    local_region ce es.scopes t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < hi ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < hi ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  v = NoneV /\
  ?out. gas_path ctx func t n (OK out) /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx (ee with scopes := es.scopes) out /\
    wb_frame ce es0 (ee with scopes := es.scopes) sa s0 out
Proof
  strip_tac >> conj_tac >- gvs[value_has_type_def] >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  drule_all (SRULE [] (Q.INST [`outs` |-> `[]`] return_successor_frame)) >> strip_tac >>
  drule_all void_outputs_counted_path >> strip_tac >>
  qexists_tac `merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx` >>
  simp[merge_callee_state_def] >>
  qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED
