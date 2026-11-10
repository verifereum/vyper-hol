(* Completed aggregate buffers: source typing and loop frames give both posts. *)
Theory bodyMemAggregateResult
Ancestors
  bodyMemAggregateBounds exprSimAggregateChildren exprSimAggregateSource
  exprSimHyps exprSimProps exprLoweringProps exprSimDefs loweringPosts
  vyperEvalExprPreservesScopesDom valueEncoding exprSimBuffer
  vyperInterpreter vyperState compileEnv context

Theorem aggregate_completed_buffer_result:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL (Value v),es') /\
  lowered_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  type_memory_size tv <= sz /\ val_in_memory tv v b r.vs_memory /\
  stmt_state_rel ctx func ce cx es t /\
  stmt_state_rel ctx func ce cx es' r /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand r = SOME (n2w b) /\
  ci_mono sa sm /\ ci_mono sm sb /\ sa.cs_next_id < sm.cs_next_id /\
  local_ptrs_reserved ce sm /\ b + sz < dimword (:256) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz) /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) /\
  (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
    FLOOKUP t.vs_allocas aid = SOME a) /\
  (!aid a n. aid < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas aid = SOME (a,n) ==> regions_disjoint b sz a n) /\
  (!name a n. local_region ce es.scopes s0 name a n ==>
    regions_disjoint b sz a n) /\
  (!name a n. local_region ce es.scopes t name a n <=>
    local_region ce es.scopes s0 name a n) /\
  (!z w. not_fresh_at sm z /\ lookup_var z t = SOME w ==>
    lookup_var z r = SOME w) /\
  (!aid a. FLOOKUP t.vs_allocas aid = SOME a ==>
    FLOOKUP r.vs_allocas aid = SOME a) /\
  (!aid a n. FLOOKUP t.vs_allocas aid = SOME (a,n) /\
    aid < sm.cs_next_id /\ (a+n <= b \/ b+sz <= a) /\
    (!name lo k. local_region ce es.scopes t name lo k ==>
      a+n <= lo \/ lo+k <= a) ==>
    mem_bytes_at a n r.vs_memory = mem_bytes_at a n t.vs_memory) /\
  t.vs_memory = s0.vs_memory /\ locals_kept ce es t r ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) p) r /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es' (Value v)
    (LocatedValue (expr_type e) p) r
Proof
  strip_tac >>
  `val_wf tv v` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[read_result_def, return_def] >> metis_tac[]) >>
  `val_footprint tv v <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!name lb len. local_region ce es'.scopes r name lb len ==>
    b + sz <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `post_value_type ce e = expr_type e` by
    metis_tac[post_value_type_lowered] >>
  conj_asm1_tac
  >- (irule buffer_loop_memory_vv_post >> simp[] >>
      qexistsl_tac [`b`, `sm`, `sz`, `t`] >>
      `b < dimword (:256)` by decide_tac >>
      gvs[arithmeticTheory.LESS_MOD,
          AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  irule aggregate_allocated_result_store_bound_mem >> simp[] >>
  conj_tac >- fs[stmt_state_rel_def] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`sa.cs_next_id`, `b`, `sz`] >>
  `b < dimword (:256)` by decide_tac >>
  simp[arithmeticTheory.LESS_MOD] >> metis_tac[]
QED
