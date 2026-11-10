Theory bodyIntCallRestoreFrame
Ancestors
  bodyIntCallCallerFrame intCallFrame loweringPosts exprLoweringProps
  compileEnv finite_map list

(* wb_frame reads its post environment only through its scopes. *)
Theorem wb_frame_scopes_cong:
  es1.scopes = es2.scopes /\ wb_frame ce es0 es1 sa s0 s ==>
  wb_frame ce es0 es2 sa s0 s
Proof
  strip_tac >>
  `locals_kept ce es0 es2 s0 s <=> locals_kept ce es0 es1 s0 s` by
    simp[locals_kept_def, popped_kept_def] >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
  pop_assum (fn lk => rewrite_tac[wb_frame_def, lk])
QED

(* Restore the caller's entire expression frame, not just its locals.
   The source scopes may have changed while evaluating the arguments. *)
Theorem wb_frame_window_bind_outputs:
  wb_frame ce es0 es' sa s0 t /\
  (!n b sz. local_region ce es0.scopes s0 n b sz ==>
    local_region ce es.scopes t n b sz) /\
  stmt_state_rel ctx func ce cx es t /\
  (!n b sz aid off asz.
    local_region ce es.scopes t n b sz /\
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
  wb_frame ce es0 es' sa s0 u
Proof
  strip_tac >> drule invoke_return_frame >> strip_tac >>
  fs[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >> irule old_alloca_window_return >>
      qexistsl_tac [`aid`,`hi`,`sa.cs_next_id`,`cs.vs_memory`,`t`] >>
      rpt conj_tac
      >- (first_assum ACCEPT_TAC)
      >- fs[stmt_state_rel_def]
      >- simp[]
      >- simp[]
      >- (qpat_x_assum `!aid off sz. _` irule >>
          conj_tac >- (first_assum ACCEPT_TAC) >>
          qexists_tac `aid` >> simp[]) >>
      simp[]) >>
  irule locals_kept_window_return >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
