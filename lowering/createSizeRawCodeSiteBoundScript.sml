(* The raw CREATE snapshot allocates at the lowered type but copies at
   the original VV tag. For an immutable source these widths coincide. *)
Theory createSizeRawCodeSiteBound
Ancestors
  createBlueprintRawCopyLayout exprPtrUnwrapStorageShape exprPtrUnwrapCode
  exprPtrUnwrapAllocSeparation bufferAllocationExecution exprSimSource
  loweringPosts compileEnv context valueEncodingProps words arithmetic

Theorem create_raw_code_snapshot_site_bound:
  expr_body_pre ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV bytes),p) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  vv_location vv = SOME LocCode /\
  vv_post H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
  compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,sm) /\
  fn_has_code a sm func ==>
  w2n (n2w (buffer_allocation_base u a.cs_next_id) : bytes32) +
    32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by
    simp[expr_body_pre_gas_obs] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL (BytesV bytes),p)` by simp[vyperStateTheory.bind_def] >>
  `vv_type vv = lowered_value_type ce e` by
    (Cases_on `vv` >> fs[vv_location_def, vv_type_def] >>
     `lowered_value_type ce e = expr_type e` by
       (irule compile_nonmemory_lowered_value_type >>
        goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[]) >>
     drule_all vv_post_code_source >> simp[is_bytestring_type_def]) >>
  `stmt_state_rel H ctx func ce cx (p with gas_obs := []) u` by fs[vv_post_def] >>
  `?rt. type_memory_bytes ce (vv_type vv) = type_memory_size rt /\
        type_memory_size rt < 2 ** 64` by
    (drule_all create_blueprint_raw_copy_layout >> strip_tac >>
     qpat_assum `type_memory_bytes ce (vv_type vv) = type_memory_size _` (irule_at Any) >>
     simp[]) >>
  pop_assum strip_assume_tac >>
  `compile_alloc_buffer (type_memory_bytes ce (vv_type vv)) a = (buf,sm)` by
    (qpat_assum `vv_type vv = lowered_value_type ce e` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all unwrap_alloc_typed_loop_bound >> strip_tac >>
  `buffer_allocation_base u a.cs_next_id < dimword (:256)` by
    (qpat_x_assum `_ + _ < 2 ** 256` mp_tac >> simp[dimword_def] >> decide_tac) >>
  `32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) = 32 * type_slot_size rt` by
    (qpat_assum `type_memory_bytes ce (vv_type vv) = type_memory_size rt` (fn th =>
       pure_rewrite_tac[th, type_memory_size_slots] >>
       simp[Once MULT_COMM, ADD_DIV_ADD_DIV])) >>
  simp[w2n_n2w, dimword_def] >>
  qpat_x_assum `_ + _ < 2 ** 256` mp_tac >> simp[] >> decide_tac
QED
