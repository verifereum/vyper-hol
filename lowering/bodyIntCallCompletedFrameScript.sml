Theory bodyIntCallCompletedFrame
Ancestors
  bodyIntCallCompletedPath bodyIntCallCallerFrame bodyIntCallRestoreFrame
  exprSimRawCallCalldata exprLoweringProps loweringPosts compileEnv
  fragGasPath fragGasFocus intCallFrame venomExecSemantics venomState
  finite_map list

Theorem counted_return_stmt_state_rel:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  (!id b sz. local_region ce es.scopes t id b sz ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ir.iret_adopt_fmp = NONE /\ EVERY (not_local_ptr ce es.scopes) outs /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  stmt_state_rel ctx func ce cx (ee with scopes := es.scopes)
    (u with vs_inst_idx := k)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  drule_all invoke_intret_data_section >> strip_tac >>
  irule stmt_state_rel_return_bind_outputs >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED

Theorem return_wb_frame_successor:
  wb_frame ce es0 es' sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce es.scopes t id b sz) /\
  stmt_state_rel ctx func ce cx es t /\
  (!id b sz aid off asz.
    local_region ce es.scopes t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < hi ==>
    regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < hi ==>
      regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  (!x. not_fresh_at sa x ==> ~MEM x outs) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  wb_frame ce es0 es' sa s0 (u with vs_inst_idx := k)
Proof
  strip_tac >> simp[raw_call_wb_frame_inst_idx] >>
  irule wb_frame_window_bind_outputs >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem return_local_region_successor:
  EVERY (not_scope_ptr ce scopes) outs /\
  bind_outputs outs vals (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  (local_region ce scopes (u with vs_inst_idx := k) id b sz <=>
   local_region ce scopes t id b sz)
Proof
  strip_tac >> drule invoke_return_frame >> strip_tac >>
  simp[local_region_def, lookup_var_def] >>
  `!p. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
        (?entry. lookup_scopes id scopes = SOME entry) ==>
        ~MEM p outs` by
    (rpt strip_tac >> fs[EVERY_MEM, not_scope_ptr_def] >> metis_tac[]) >>
  eq_tac >> strip_tac >>
  qexistsl_tac [`entry`,`p`,`w`] >> simp[] >>
  `~MEM p outs` by metis_tac[] >>
  qpat_x_assum `!x. ~MEM x outs ==> _` drule >>
  simp[lookup_var_def]
QED
