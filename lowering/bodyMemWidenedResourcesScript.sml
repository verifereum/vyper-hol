(* Allocation resources for a physical widened aggregate field. *)
Theory bodyMemWidenedResources
Ancestors
  bodyMemAggregateBounds exprSimAggregateChildren exprSimHyps
  loweringPosts exprLoweringProps valueEncoding venomState words

Theorem aggregate_owned_copy_resources_mem:
  expr_val_own ce cx sty sa sb es v op s /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  0 < type_memory_size stv /\
  eval_operand op s = SOME sw /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+k ==>
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next
Proof
  strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_own_def] >> strip_tac >> gvs[] >>
  `aid <> did` by decide_tac >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] aggregate_allocated_source_bounds) >> strip_tac >>
  `b + k <= s.vs_alloca_next` by
    (irule aggregate_alloca_capacity_mem >> metis_tac[]) >>
  `b' + sz <= s.vs_alloca_next` by
    (irule aggregate_alloca_capacity_mem >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  decide_tac
QED
