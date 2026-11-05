(* Boundary probe: the live value extent, not its full static capacity,
   is the range available to the bytestring adapter. *)
Theory bodyIfExpMemoryAdapter
Ancestors
  bodyMemoryDefs loweringPosts instMemFrontier compileEnv
  finite_map arithmetic

Theorem ifexp_located_footprint_frontier:
  vv_at ce cx t sa sb es raw (LocatedValue t' p) s /\
  p.ptr_location = LocMemory /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  0 < val_footprint tv v /\
  stmt_state_rel ctx func ce cx es s /\ alloca_next_valid s ==>
  w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac
  >- (drule_all alloca_region_below_frontier >> simp[]) >>
  drule_all body_local_region_frontier >> decide_tac
QED
