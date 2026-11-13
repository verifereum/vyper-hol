(* Value and nonwriting statement branches of the selected-prefix schema. *)
Theory guardSourceOrdinaryValues
Ancestors
  list guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeSystem vyperTypeCallGraph vyperEvalMisc vyperStorageTrace vyperTypeEvalSoundness
  vyperPlaceFrames
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

Theorem finite_prefix_Expr_StructLit:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_StructLit")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs (MAP SND kes))` by
    (qpat_x_assum `call_evaluation_safe cx (int_calls_expr (StructLit _ _ _))` mp_tac >>
     simp_tac(srw_ss())[Once int_calls_expr_def,
       vyperTypeEvalSoundnessTheory.int_calls_exprs_MAP_SND]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule vyperTypeEvalSoundnessTheory.well_typed_named_exprs_MAP_SND_stmt >> simp[]) >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, LET_THM, bind_def, return_def] >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _` (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st`] mp_tac) >>
  disch_then (qspecl_then [`FST (eval_exprs cx (MAP SND kes) st)`, `s1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[APPEND] >> metis_tac[])) >> simp[]
QED

Theorem finite_prefix_Expr_TypeBuiltin:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_TypeBuiltin")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (TypeBuiltin ty tb typ es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (TypeBuiltin _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `well_typed_exprs env es` by
    (qpat_x_assum `well_typed_expr env (TypeBuiltin _ _ _ _)` mp_tac >>
     simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def] >>
  reverse (Cases_on `type_builtin_args_length_ok tb (LENGTH es)`)
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `!s'' x t. type_check _ _ s'' = (INL x,t) ==> _` kall_tac >>
      gvs[valid_horizon_def]) >>
  simp_tac(srw_ss())[] >>
  qpat_x_assum `!s'' x t. _` (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  asm_rewrite_tac[type_check_def, assert_def, return_def] >> strip_tac >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[] >> strip_tac >>
  `st' = s1` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     gvs[AllCaseEqs()] >> imp_res_tac lift_sum_state >> gvs[]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st`] mp_tac) >>
  disch_then (qspecl_then [`FST (eval_exprs cx es st)`, `s1`] mp_tac) >>
  rpt (qpat_x_assum `s1 = s1` kall_tac) >>
  (impl_tac >- (asm_rewrite_tac[APPEND] >> metis_tac[])) >> simp[]
QED

Theorem finite_prefix_RaiseCustomError:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "RaiseCustomError")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, well_typed_custom_error_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  Cases_on `err` >>
  Cases_on `get_module_code cx (FST p)`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def, valid_horizon_def] >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def, valid_horizon_def] >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def, valid_horizon_def] >>
  rename1 `order_custom_error_args params (CustomError p positional kwargs) = SOME es` >>
  first_x_assum (drule_at (Pat `order_custom_error_args _ _ = _`)) >>
  simp[] >> strip_tac >>
  `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
    (drule vyperASTTheory.order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by
    (drule well_typed_exprs_perm >> disch_then (qspec_then `env` mp_tac) >>
     simp[vyperASTTheory.custom_error_exprs_def]) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (drule call_evaluation_safe_exprs_perm >>
     disch_then (qspec_then `cx` mp_tac) >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,s1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[] >> strip_tac >>
  `st' = s1` by
    (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     gvs[AllCaseEqs(), bind_def, return_def, raise_def] >>
     Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x` >>
     gvs[return_def, raise_def]) >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st`] mp_tac) >>
  disch_then (qspecl_then [`FST (eval_exprs cx es st)`, `s1`] mp_tac) >>
  rpt (qpat_x_assum `s1 = s1` kall_tac) >>
  (impl_tac >-
    (asm_rewrite_tac[APPEND] >> conj_tac
     >- (qexists `sfx` >> simp[]) >>
     pure_rewrite_tac[APPEND] >>
     qpat_x_assum `!pre rq co sfx. _` mp_tac >>
     asm_rewrite_tac[] >> simp[APPEND])) >> simp[]
QED

Theorem finite_prefix_TargetPlace:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TargetPlace")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[well_typed_target_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac get_place_state >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED

Theorem lookup_global_backend_observations[local]:
  lookup_global cx src n st = (res,st') ==>
  (storage_trace_backends_well_formed cx R st'.storage_trace <=>
   storage_trace_backends_well_formed cx R st.storage_trace)
Proof
  Cases_on `get_module_code cx src` >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `find_var_decl_by_name n x` >>
  simp[get_immutables_def, get_address_immutables_def, bind_def, return_def, raise_def] >>
  TRY (PairCases_on `x'` >> Cases_on `x'0`) >>
  gvs[bind_def, ignore_bind_def, lift_option_type_def, return_def, raise_def,
      record_storage_event_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[storage_trace_backends_well_formed_def]
QED

Theorem finite_prefix_Expr_TopLevelName:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_TopLevelName")
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def] >> strip_tac >>
  `st'.accounts = st.accounts /\ st'.tStorage = st.tStorage` by
    (drule lookup_global_state >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `storage_trace_backends_well_formed cx (FST H) st'.storage_trace` by
    metis_tac[valid_horizon_def, storage_observations_ok_def, lookup_global_backend_observations] >>
  gvs[storage_observations_ok_def, storage_trace_regions_append,
      storage_trace_locks_append, EVERY_APPEND,
      storage_well_formed_on_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b slot tv. _` drule >>
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem finite_prefix_BasePlaceRoot_TopLevelNameTarget:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "BasePlaceRoot_TopLevelNameTarget")
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def] >> strip_tac >>
  `st'.accounts = st.accounts /\ st'.tStorage = st.tStorage` by
    (drule lookup_global_state >> disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `storage_trace_backends_well_formed cx (FST H) st'.storage_trace` by
    metis_tac[valid_horizon_def, storage_observations_ok_def, lookup_global_backend_observations] >>
  gvs[storage_observations_ok_def, storage_trace_regions_append,
      storage_trace_locks_append, EVERY_APPEND,
      storage_well_formed_on_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b slot tv. _` drule >>
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem extend_place_backend_observations[local]:
  extend_place cx pv sb st = (res,st') ==>
  (storage_trace_backends_well_formed cx R st'.storage_trace <=>
   storage_trace_backends_well_formed cx R st.storage_trace)
Proof
  Cases_on `pv`
  >- simp[extend_place_def, raise_def]
  >- (strip_tac >> drule extend_place_PlaceR_state >> simp[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, ignore_bind_def, record_storage_event_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, ignore_bind_def,
    record_storage_event_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[storage_trace_backends_well_formed_def]
QED

Theorem select_result_backend_observations[local]:
  select_result cx ty pv sb st = (res,st') ==>
  (storage_trace_backends_well_formed cx R st'.storage_trace <=>
   storage_trace_backends_well_formed cx R st.storage_trace)
Proof
  Cases_on `pv` >>
  simp[select_result_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  metis_tac[extend_place_backend_observations]
QED

Theorem finite_prefix_Expr_Attribute:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Attribute")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (Attribute ty e id) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `well_typed_expr env (Attribute ty e id) ==>
   storage_well_formed_on cx st' (FST H) /\
   storage_observations_ok cx H st'.storage_trace` suffices_by
    (simp_tac(srw_ss())[well_typed_expr_def] >> metis_tac[]) >>
  disch_tac >>
  `well_typed_expr env e` by
    (qpat_x_assum `well_typed_expr env (Attribute ty e id)` mp_tac >>
     simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`, `env`, `st`, `res`, `st'`] mp_tac) >>
      (impl_tac >- (asm_rewrite_tac[APPEND] >> metis_tac[])) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_select] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _`
      (qspecl_then [`initial_st`, `selected`, `env`, `st`, `INL x`, `st1`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[APPEND] >> metis_tac[APPEND_ASSOC])) >> metis_tac[]) >>
  `storage_trace_backends_well_formed cx (FST H) st'.storage_trace` by
    metis_tac[select_result_backend_observations, storage_observations_ok_def] >>
  qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
  conj_tac
  >- (drule select_result_state >> disch_then SUBST1_TAC >>
      qpat_x_assum `storage_well_formed_on cx st1 _` mp_tac >>
      simp_tac(srw_ss())[storage_well_formed_on_def, vyperStorageBackendTheory.get_storage_def]) >>
  gvs[storage_observations_ok_def, storage_trace_regions_append,
      storage_trace_locks_append, EVERY_APPEND]
QED

Theorem finite_prefix_AssertReason:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "AssertReason")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _` kall_tac >>
      simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[switch_BoolV_def, bind_def, return_def, raise_def] >>
  qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >> strip_tac >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`) >> simp_tac(srw_ss())[]
  >- (strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e' ==> _) /\ _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  Cases_on `x' = BoolV T` >>
  pop_assum (fn th => rewrite_tac[th, return_def, raise_def]) >>
  simp_tac(srw_ss())[]
  >- (strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e' ==> _) /\ _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  reverse (Cases_on `x' = BoolV F`) >>
  pop_assum (fn th => rewrite_tac[th, return_def, raise_def]) >>
  simp_tac(srw_ss())[]
  >- (strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e' ==> _) /\ _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  qmatch_goalsub_rename_tac `eval_expr cx reason` >>
  Cases_on `eval_expr cx reason st1` >> rename1 `eval_expr cx reason st1 = (er2,st3)` >>
  simp_tac(srw_ss())[bind_def, return_def, raise_def] >> strip_tac >>
  `st' = st3` by
    (ntac 2 (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac) >>
     Cases_on `er2` >> gvs[AllCaseEqs()] >> imp_res_tac read_result_state >>
     imp_res_tac lift_option_type_state >> gvs[raise_def]) >>
  pop_assum SUBST_ALL_TAC >>
  `?suffix. st3.storage_trace = st1.storage_trace ++ suffix` by
    (ntac 2 (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac) >>
     metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame]) >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e ==> _) /\ _`
      (qspecl_then [`initial_st`, `selected`, `env`, `st`, `INL x`, `st1`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[APPEND] >> metis_tac[APPEND_ASSOC])) >>
     disch_then (mp_tac o CONJUNCT1) >> asm_rewrite_tac[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `IS_SOME st1.outcomes` by
    (qpat_assum `eval_expr cx e st = _`
       (mp_then Any mp_tac (cj 5 eval_outcome_suffix_mutual)) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e ==> _) /\ _` kall_tac >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED
