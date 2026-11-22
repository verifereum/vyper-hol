Theory createSizeRawSource
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimHyps exprSimSource allocLimits supportedExprTraverse
  exprSimMemorySource vyperState vyperValue vyperTyping vyperAST
  vyperStatePreservation
  vyperTypeSystem vyperTypeCallGraph vyperInterpreter vyperStorageTrace
  vyperCreate gasOutcomeFull loweringPosts list rich_list

Theorem create_raw_arg_body_pre:
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) args df) es /\
  MEM e args /\ expr_sim_inv ce cx env p ==>
  expr_body_pre ce cx env e p
Proof
  rw[expr_body_pre_split_def, expr_body_pre_mods_def, well_typed_expr_def,
     int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every,
     expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[int_calls_exprs_every_mem, well_typed_exprs_member,
    byte_widths_exprs_mem, alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem,
    expr_sim_inv_split_def]
QED

Theorem create_raw_first_type:
  well_typed_expr env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) ==>
  ?n. n <= 49152 /\ expr_type e = BaseT (BytesT (Dynamic n)) /\ (hs ==> rest <> [])
Proof
  simp[well_typed_expr_def, create_arg_types_ok_def] >>
  Cases_on `hs` >> simp[] >> rpt strip_tac >> gvs[] >> CCONTR_TAC >> gvs[]
QED

Theorem create_raw_call_split:
  eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) =
  bind (eval_expr cx e) (\tv.
    bind (read_result cx tv) (\b.
      bind (eval_exprs cx
        (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
           v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
        (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
           (blueprint_literal_offset cx hs (e::v::rest)) (b::vs))))
Proof
  simp[Once evaluate_def, create_operand_order_def, Once evaluate_def,
       bind_assoc, bind_def, return_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >> simp[] >> Cases_on `q` >> simp[]
QED

Theorem create_raw_cont_horizon:
  eval_expr cx e es = (res,p) /\
  bind (eval_expr cx e) (\tv. bind (read_result cx tv) (\code.
    bind (eval_exprs cx args) (\vs. eval_create_operands cx RawCreate hs rof tys lit
      (code::vs)))) es = (r,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H p.storage_trace
Proof
  strip_tac >>
  qpat_x_assum `bind (eval_expr _ _) _ _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split) >>
  strip_tac >> gvs[] >>
  `storage_trace_frame (bind (read_result cx x) (\code.
     bind (eval_exprs cx args) (\vs. eval_create_operands cx RawCreate hs rof tys lit
       (code::vs))))` by
    simp[storage_trace_frame_bind_all, storage_trace_frame_read_result,
         evaluate_storage_trace_frame, storage_trace_frame_create_operands] >>
  drule_all storage_trace_frame_prefix >> strip_tac >>
  metis_tac[valid_horizon_append]
QED

Theorem create_raw_read_bytes:
  expr_body_pre ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,p) /\
  vv_post H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u ==>
  ?code. LENGTH code <= n /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := [])
Proof
  strip_tac >>
  `?val. read_result cx tv (p with gas_obs := []) = (INL val,p with gas_obs := [])` by
    (fs[vv_post_def] >> Cases_on `vv` >> fs[vv_holds_def] >>
     Cases_on `p' .ptr_location` >>
     fs[storage_holds_def, immutable_holds_def]) >>
  `read_result cx tv p = (INL val,p)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >>
     disch_then (qspec_then `p.gas_obs` mp_tac) >> simp[]) >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt val` by metis_tac[] >>
  qpat_x_assum `evaluate_type _ _ = SOME _` mp_tac >>
  simp[] >> simp[evaluate_type_def] >> strip_tac >>
  Cases_on `val` >> gvs[value_has_type_def]
QED
