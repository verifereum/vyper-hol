Theory bodyIntCallAssemblyFrame
Ancestors
  bodyIntCallCompletedFrame bodyIntCallCallerFrame bodyIntCallAssembly
  compileEnv exprLoweringProps loweringPosts venomExecSemantics venomState
  fragGasFocus fragGasPath finite_map list

Theorem return_successor_frame:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
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
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ir.iret_adopt_fmp = NONE /\ EVERY (not_local_ptr ce es.scopes) outs /\
  EVERY (not_scope_ptr ce es.scopes) outs /\
  (!x. not_fresh_at sa x ==> ~MEM x outs) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  stmt_state_rel ctx func ce cx (ee with scopes := es.scopes)
    (u with vs_inst_idx := k) /\
  wb_frame ce es0 (ee with scopes := es.scopes) sa s0 (u with vs_inst_idx := k) /\
  (!id b sz. local_region ce es.scopes (u with vs_inst_idx := k) id b sz <=>
    local_region ce es.scopes t id b sz)
Proof
  strip_tac >>
  `!id b sz. local_region ce es.scopes t id b sz ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory` by
    (rpt strip_tac >> irule window_frame_local_regions >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac >- (irule counted_return_stmt_state_rel >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
    metis_tac[]) >>
  conj_tac >- (irule wb_frame_scopes_cong >> qexists_tac `es` >> simp[] >>
    irule return_wb_frame_successor >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[] >>
    goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  rpt gen_tac >> irule return_local_region_successor >>
  goal_assum (drule_at Any) >> simp[]
QED
