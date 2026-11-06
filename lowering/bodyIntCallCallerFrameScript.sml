Theory bodyIntCallCallerFrame
Ancestors
  bodyIntCallReturnFrame bodyIntCallReturnSource bodyIntCallReturnBoundaryChecks
  bodyMemoryDefs exprLoweringProps compileEnv venomExecSemantics venomState
  finite_map list

Theorem window_frame_local_regions:
  stmt_state_rel ctx func ce cx es t /\
  (!n b sz aid off asz.
    local_region ce es.scopes t n b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ lo <= aid /\ aid < hi ==>
    regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      lo <= aid /\ aid < hi ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz mem = mem_bytes_at b sz t.vs_memory) ==>
  !n b sz. local_region ce es.scopes t n b sz ==>
    mem_bytes_at b sz mem = mem_bytes_at b sz t.vs_memory
Proof
  rpt strip_tac >>
  `b + sz <= t.vs_alloca_next` by
    (drule_all body_local_region_frontier >> simp[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem stmt_state_rel_return_bind_outputs:
  stmt_state_rel ctx func ce cx es t /\
  state_rel other ce cx (ee with scopes := []) cs /\
  cs.vs_data_section = t.vs_data_section /\
  immutable_alloca_sep func ce cx (ee with scopes := es.scopes) t /\
  (!n b sz. local_region ce es.scopes t n b sz ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ir.iret_adopt_fmp = NONE /\ EVERY (not_local_ptr ce es.scopes) outs /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  stmt_state_rel ctx func ce cx (ee with scopes := es.scopes) u
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx (ee with scopes := es.scopes)
     (merge_callee_state t cs)` by
    (irule stmt_state_rel_merge_callee >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule stmt_state_rel_bind_outputs >>
  gvs[adopt_return_fmp_def] >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem setup_run_intret_data_section:
  setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs ==>
  cs.vs_data_section = t.vs_data_section
Proof
  strip_tac >> drule intCallReturnTheory.run_blocks_intret_data_section >>
  gvs[setup_callee_def, AllCaseEqs()]
QED
