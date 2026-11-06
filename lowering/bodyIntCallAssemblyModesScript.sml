Theory bodyIntCallAssemblyModes
Ancestors
  bodyIntCallAssemblyFrame bodyIntCallCompletedModes bodyIntCallCompletedFrame
  compileEnv exprLoweringProps loweringPosts venomExecSemantics venomState
  fragGasFocus fragGasPath finite_map list

Theorem void_return_endpoint:
  emit_void INVOKE ops si = ((),sb) /\ fn_has_code si sb func /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  expr_type e = NoneT /\ value_has_type NoneTV v /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  wb_frame ce es0 sa s0 t /\
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
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 (ee with scopes := es.scopes) (Value v)
      (StackValue NoneT (Lit 0w)) out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `bind_outputs [] ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) =
    SOME (merge_callee_state t cs)` by
    simp[bind_outputs_def, adopt_return_fmp_def] >>
  drule_all (SRULE [] (Q.INST [`outs` |-> `[]`] return_successor_frame)) >>
  strip_tac >>
  qexists_tac `0` >> simp[] >> irule void_completed_endpoint >> simp[] >>
  conj_tac >- (qexistsl_tac [`ops`,`si`] >> simp[]) >>
  qexistsl_tac [`callee`,`cs`,`entered`,`ir`] >> simp[]
QED
