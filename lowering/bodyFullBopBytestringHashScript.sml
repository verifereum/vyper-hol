Theory bodyFullBopBytestringHash
Ancestors
  bodySimFull bodyFullGhostFrame bodyPtrBopTypedSource bodyPtrBopHashRun
  bodyPtrBopHashCompile bodyPtrBopHashEndpoint bodyPtrBopHashFootprint
  bodyPtrBopHashSuffix bodyPtrBopHashFrame bodyMemBopHeldHash
  fragGasCopyLoop fragGasSeqPtr gasOutcomeFullCompose
  bytestringHashProps exprSimHashBoundary exprSimHash exprSimHyps exprLoweringProps
  exprSimProps bodyFullPreds bodyPtrDefs gasStorage vyperStorageTrace
  loweringPosts exprSimMemDefs allocaHistoryFragment
  gasOutcomeFull exprOperandVar exprLowering compileEnv vyperTyping
  vyperValue vyperInterpreter venomState list vyperStorageFootprint
Libs pairLib

Theorem bop_bytestring_hash_post_view:
  is_bytestring_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  body_inv tops ctx cenv cx /\
  lower_value compile_expr cenv (expr_type e) e sa = (m,cb) /\
  compile_bytestring_hash m cb = (h,sz) /\
  fn_has_code sa sz func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es sa cb s ee v m t /\
      expr_store_bound cx (expr_type e) v m t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee HG un t /\
      ptr_val_ok cx (post_value_type cenv e) v m HG un t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e m HG t) /\
      ghost_kept_at lo cenv es sa G tn s HG un) /\
  (?gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
        (res,ee)) ==>
  ?v tv p w contents b.
    res = INL v /\ m = Var p /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
    ~is_word_type (expr_type e) /\
    expr_val_at cenv cx (expr_type e) sa cb ee v (Var p) t /\
    ptr_val_ok cx (expr_type e) v (Var p) HG un t /\
    lookup_var p t = SOME w /\ not_fresh_at cb p /\
    (v = BytesV contents \/
     ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
    w = n2w b /\ mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
    mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
    b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
      ee.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by
    (drule bop_typed_source_witness >>
     disch_then (qspecl_then [`v`, `ee`] mp_tac) >> simp[] >> metis_tac[]) >>
  `~is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `expr_val_at cenv cx (expr_type e) sa cb ee v m t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     gvs[expr_post_def, post_value_type_bytestring]) >>
  `?w. eval_operand m t = SOME w` by metis_tac[expr_val_at_def] >>
  `val_footprint tv v <> 0` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
     Cases_on `v` >> gvs[evaluate_type_def, value_has_type_def, val_footprint_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, evaluate_type_def, value_has_type_def, val_footprint_def]) >>
  `?p. m = Var p` by
    metis_tac[ptr_val_ok_def, ptr_mem_ok_def, post_value_type_bytestring] >>
  gvs[] >>
  `lookup_var p t = SOME w` by gvs[eval_operand_def] >>
  `not_fresh_at cb p` by metis_tac[compile_lower_value_var] >>
  `?contents b.
     (v = BytesV contents \/ ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
     w = n2w b /\ mem_word_at b t.vs_memory = n2w (LENGTH contents) /\
     mem_bytes_at (b + 32) (LENGTH contents) t.vs_memory = contents /\
     b + 32 < dimword(:256) /\ LENGTH contents < dimword(:256)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
     >- (gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> _`
           (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         drule hash_string_post_view >> simp[evaluate_type_def] >> strip_tac >>
         metis_tac[optionTheory.SOME_11, LENGTH_MAP]) >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def] >>
     gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule hash_dynamic_post_view >> simp[evaluate_type_def] >> strip_tac >>
     metis_tac[optionTheory.SOME_11]) >>
  qexistsl_tac [`contents`, `b`] >> simp[]
QED
