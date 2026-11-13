(* Counted continuation boundaries for widened aggregate place assignment. *)
Theory placeAssignContinuationMem
Ancestors
  placeStorageNormalizationBoundary placeMemoryStagingBoundary
  externalNormalizePremises typedMemoryRankCounted placeStorageFixedCounted
  placeStorageDynamicEndpoint placeStore loweringPosts
  exprSimAlloc exprLoweringProps externalReturnNormalizeMem venomInst exprSimDefs

Theorem place_normalization_source_separate[local]:
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sb /\ expr_val_at ce cx sty sa sb es v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ value_has_type tv v /\
  eval_operand src s = SOME p ==>
  0 < type_memory_size tv /\
  (!b sz. FLOOKUP s.vs_allocas sb.cs_next_id = SOME (b,sz) ==>
    w2n p + type_memory_size tv <= b \/ b + sz <= w2n p)
Proof
  strip_tac >> drule_all normalize_return_source_kinds >> strip_tac >>
  `0 < type_memory_size tv` by metis_tac[normalize_return_source_positive] >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[normalize_nonbytes_footprint] >>
  simp[] >> rpt strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `not_local_ptr ce es.scopes (STRING #"%" (toString sb.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) normalize_alloca_source_separate >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >>
  simp[mk_inst_def] >> goal_assum (drule_at Any) >>
  qexists_tac `ctx` >> simp[mk_inst_def]
QED

(* Unlike the raw allocation boundary this has no caller replay obligation. *)
Theorem place_normalization_allocation_mem:
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sb /\ expr_val_at ce cx sty sa sb es v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ value_has_type tv v /\
  expr_val_rel cx sty v src s /\
  eval_operand src s = SOME p /\ n < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sb x) /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?u w. gas_path_mem ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\ alloca_history func u /\
    eval_operand src u = SOME p /\ eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n p) u.vs_memory /\
    w2n p + type_memory_size tv <= u.vs_alloca_next /\
    w2n p + type_memory_size tv < dimword (:256) /\
    w2n w + n <= u.vs_alloca_next /\ w2n w + n < dimword (:256) /\
    (w2n p + type_memory_size tv <= w2n w \/ w2n w + n <= w2n p) /\
    FLOOKUP u.vs_allocas sb.cs_next_id = SOME (w2n w,n) /\
    u.vs_memory = s.vs_memory /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) n b len) /\
    (?out. buf.buf_operand = Var out /\ not_fresh_at sc out) /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\ u.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all place_normalization_source_separate >> strip_tac >>
  drule_all normalize_return_source_kinds >> strip_tac >>
  drule_all normalize_source_window >> strip_tac >> gvs[] >>
  `w2n p + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  `val_in_memory tv v (w2n p) s.vs_memory` by
    gvs[expr_val_at_def, expr_val_rel_def] >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)
    storage_normalization_allocation_boundary >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`src`,`p`,`tv`,`v`] mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`u`,`w`] strip_assume_tac) >>
  qexistsl_tac [`u`,`w`] >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
