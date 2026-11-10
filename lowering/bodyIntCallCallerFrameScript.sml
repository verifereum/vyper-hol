Theory bodyIntCallCallerFrame
Ancestors
  bodyIntCallReturnFrame bodyIntCallReturnSource bodyIntCallReturnBoundaryChecks
  bodyMemoryDefs exprLoweringProps compileEnv venomExecSemantics venomState
  finite_map list exprSimProps loweringPosts venomMemDefs

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

(* Whole-region agreement composes the entry frame without identifying the
   saved caller scopes with the scopes before argument evaluation. *)
Theorem locals_kept_window_return:
  locals_kept ce es0 es' s0 t /\
  (!n b sz. local_region ce es0.scopes s0 n b sz ==>
    local_region ce es.scopes t n b sz) /\
  stmt_state_rel ctx func ce cx es t /\
  (!n b sz aid off asz.
    local_region ce es.scopes t n b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ lo <= aid /\ aid < hi ==>
    regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      lo <= aid /\ aid < hi ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz mem = mem_bytes_at b sz t.vs_memory) /\
  u.vs_memory = mem ==>
  locals_kept ce es0 es' s0 u
Proof
  strip_tac >> irule locals_kept_regions_tail >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  irule window_frame_local_regions >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

(* Old ids cannot coincide with the call-window ids. The allocation invariant,
   not an assumed ordering of addresses, provides the required separation. *)
Theorem old_alloca_window_return:
  alloca_inv t /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ aid < lo /\
  (!b n. b + n <= t.vs_alloca_next /\
    (!id p k. FLOOKUP t.vs_allocas id = SOME (p,k) /\
      lo <= id /\ id < hi ==> regions_disjoint b n p k) ==>
    mem_bytes_at b n mem = mem_bytes_at b n t.vs_memory) /\
  mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz initial /\
  u.vs_memory = mem ==>
  mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz initial
Proof
  strip_tac >> gvs[] >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory` suffices_by simp[] >>
  qpat_x_assum `!b n. _ ==> mem_bytes_at _ _ _ = _` irule >>
  reverse conj_tac
  >- (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `aid <> id` by decide_tac >>
  fs[alloca_inv_def, allocas_non_overlapping_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
