(* Owned child allocations give separated typed-copy windows, independently
   of the order in which allocation sites are visited at runtime. *)
Theory bodyMemAggregateOwnership
Ancestors
  exprSimAggregateChildren exprSimMemDefs exprLoweringProps venomMemDefs
  loweringPosts finite_map words

Theorem aggregate_owned_child_copy_windows:
  vv_own ce cx sty sa sb ee raw (LocatedValue vt p) s /\
  p.ptr_location = LocMemory /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_bytestring_type sty /\ type_memory_size stv <> 0 /\
  eval_operand p.ptr_operand s = SOME sw /\
  stmt_state_rel ctx func ce cx ee s /\ alloca_inv s /\
  FLOOKUP s.vs_allocas parent = SOME (b,n) /\
  parent < sa.cs_next_id /\ off + type_memory_size dtv <= n ==>
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  b+off + type_memory_size dtv <= s.vs_alloca_next /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  b+off + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= b+off \/
   b+off + type_memory_size dtv <= w2n sw)
Proof
  strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    (irule evaluated_nonbytes_footprint >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  fs[vv_own_def] >>
  `aid <> parent` by decide_tac >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= b+off \/
    b+off + type_memory_size dtv <= w2n sw)` by
    (irule aggregate_allocated_source_bounds >>
     qexistsl_tac [`b'`, `aid`, `b`] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `aid <> parent`)) >> simp[]) >>
  fs[alloca_inv_def, alloca_next_valid_def] >>
  `b'+sz <= s.vs_alloca_next /\ b+n <= s.vs_alloca_next` by
    metis_tac[] >> decide_tac
QED
