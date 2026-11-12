(* Value and nonwriting statement branches of the selected-prefix schema. *)
Theory guardSourceOrdinaryValues
Ancestors
  list guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeSystem vyperTypeCallGraph vyperEvalMisc vyperStorageTrace
  vyperTypeStmtSoundness vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperEvalOutcomeSuffix vyperTypeEvalStoragePreservation vyperStatePreservation
Libs
  guardSourceSchemaLib

Theorem finite_prefix_Pass:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Pass")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_Continue:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Continue")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_Break:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Break")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_Return_NONE:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Return_NONE")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_RaiseBare:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "RaiseBare")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_RaiseUnreachable:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "RaiseUnreachable")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_Expr_Literal:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Literal")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_Expr_FlagMember:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_FlagMember")
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_flag_mem_state >> gvs[valid_horizon_def]
QED

Theorem finite_prefix_Expr_Name:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Name")
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[valid_horizon_def]
QED

Theorem finite_prefix_Return_SOME:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Return_SOME")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def] >> strip_tac >>
  `st' = s1` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     gvs[AllCaseEqs(), raise_def] >> imp_res_tac read_result_state >> gvs[raise_def]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

Theorem finite_prefix_Expr:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Expr e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[] >> strip_tac >>
  qpat_x_assum `s1 = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

Theorem finite_prefix_AssertBare:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "AssertBare")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >>
  strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def] >> strip_tac >>
  `st' = s1` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     imp_res_tac switch_BoolV_state >> gvs[return_def, raise_def]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

Theorem finite_prefix_AssertUnreachable:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "AssertUnreachable")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >>
  strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def] >> strip_tac >>
  `st' = s1` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     imp_res_tac switch_BoolV_state >> gvs[return_def, raise_def]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

Theorem finite_prefix_RaiseReason:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "RaiseReason")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def] >> strip_tac >>
  `st' = s1` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     gvs[AllCaseEqs(), raise_def] >> imp_res_tac read_result_state >>
     imp_res_tac lift_option_type_state >> gvs[raise_def]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

Theorem finite_prefix_BasePlaceRoot_NameTarget:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "BasePlaceRoot_NameTarget")
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[valid_horizon_def]
QED

Theorem finite_prefix_Log:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Log")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, return_def, raise_def] >> strip_tac >>
  `st'.accounts = s1.accounts /\ st'.tStorage = s1.tStorage /\
   st'.outcomes = s1.outcomes /\ st'.storage_trace = s1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     gvs[lift_option_def, bind_def, return_def, raise_def, push_log_def,
         check_not_static_def, check_def, assert_def, ignore_bind_def, AllCaseEqs()] >>
     Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
     gvs[return_def, raise_def]) >>
  `storage_well_formed_on cx s1 (FST H) /\
   storage_observations_ok cx H s1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _`
      (qspecl_then [`initial_st`, `selected`] irule) >> metis_tac[]) >>
  conj_tac >- (metis_tac[storage_well_formed_on_backends]) >>
  metis_tac[]
QED
