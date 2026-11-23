(* Resolve a custom error and supply the argument simulation with its source premises. *)
Theory bodyFullCustomErrorSource
Ancestors
  bodySim bodyExprPreFacts bodySimLogArgs exprSimSource exprSimHypsDefs
  allocLimits allocLimitsProps compileEnv supportedStmts supportedExprs supportedStmtTraverse
  supportedExprTraverse vyperInterpreter vyperTypeSystem vyperTypeContract
  vyperTypeCallGraph vyperContext vyperAST list alist
  bodyStorageCases bodyFullPreds bodySimFull reasonSourceProps stmtSimDefs
  gasContext gasOutcome vyperExprNoControl vyperState stmtSimIfProps exprSimDefs
  compileVyper vyperTypeCallStackSoundness
  bodyQualifiedStmtSupport
Libs
  monadsyntax

Theorem custom_error_raise_source:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Raise (RaiseCustomError (CustomError id pos kw))) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Raise (RaiseCustomError (CustomError id pos kw))) ==>
     occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Raise (RaiseCustomError (CustomError id pos kw))) = SOME env' /\
  stmt_exprs_ok cenv (Raise (RaiseCustomError (CustomError id pos kw))) /\
  call_evaluation_safe cx
    (int_calls_stmt (Raise (RaiseCustomError (CustomError id pos kw)))) ==>
  ?params args.
    args = custom_error_exprs (CustomError id pos kw) /\
    get_module_code cx (FST id) = SOME tops /\
    lookup_custom_error_args_in (SND id) tops = SOME params /\
    order_custom_error_args params (CustomError id pos kw) = SOME args /\
    cenv.ce_error_info (nsid_to_string id) = SOME params /\
    MAP expr_type args = MAP SND params /\
    custom_error_alloc_ok cenv (CustomError id pos kw) /\
    eval_stmt cx (Raise (RaiseCustomError (CustomError id pos kw))) =
      bind (eval_exprs cx args) (\vs. bind
        (lift_option (build_custom_error_data (get_tenv cx) (SND id)
          (MAP SND params) vs) "custom error encoding")
        (\data. raise (Error (RevertData data)))) /\
    !e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
      expr_body_pre cenv cx env e st
Proof
  strip_tac >>
  `get_module_code cx NONE = SOME tops /\ cenv_module_pins tops cenv` by
    fs[body_inv_def] >>
  `FST id = NONE` by
    (PairCases_on `id` >> Cases_on `id0` >>
     fs[stmt_exprs_ok_def, cenv_module_pins_def,
        custom_error_resolved_def, ALOOKUP_def]) >>
  PairCases_on `id` >> gvs[] >>
  `custom_error_resolved [(NONE,tops)] (CustomError (NONE,id1) pos kw) /\
   EVERY (supported_pure_expr tops) (custom_error_exprs (CustomError (NONE,id1) pos kw))` by
    fs[Once supported_stmt_def, supported_raise_reason_def, supported_custom_error_def] >>
  gvs[custom_error_resolved_def, ALOOKUP_def] >>
  rename1 `lookup_custom_error_args_in name tops` >>
  Cases_on `lookup_custom_error_args_in name tops` >> gvs[] >>
  rename1 `lookup_custom_error_args_in name tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError (NONE,name) pos kw)` >> gvs[] >>
  rename1 `order_custom_error_args params _ = SOME args` >>
  `args = custom_error_exprs (CustomError (NONE,name) pos kw)` by
    (qpat_x_assum `order_custom_error_args params _ = SOME _` mp_tac >>
     rw[order_custom_error_args_def, custom_error_exprs_def] >>
     imp_res_tac order_custom_error_kwargs_SOME >> gvs[NULL_EQ]) >>
  `cenv.ce_error_info (nsid_to_string (NONE,name)) = SOME params` by
    fs[cenv_module_pins_def, nsid_to_string_def] >>
  qpat_x_assum `args = custom_error_exprs _` SUBST_ALL_TAC >>
  simp[Once evaluate_def] >>
  conj_tac >- fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  mp_tac (Q.INST [`args` |-> `custom_error_exprs (CustomError (NONE,name) pos kw)`,
     `tops` |-> `tops`, `ctx` |-> `ctx`, `cenv` |-> `cenv`,
     `cx` |-> `cx`, `env` |-> `env`] body_log_snapshot_expr_pre) >>
  impl_tac >| [ALL_TAC, disch_then ACCEPT_TAC] >>
  `!P. supported_stmt_expr_exists P (Raise (RaiseCustomError (CustomError (NONE,name) pos kw))) <=>
       supported_exprs_exists P (custom_error_exprs (CustomError (NONE,name) pos kw))` by
    simp[supported_stmt_expr_exists_def, supported_raise_exists_def,
         supported_exprs_exists_every, EXISTS_MEM] >>
  drule_all body_inv_stmt_const_name_free >> strip_tac >>
  fs[Once type_stmt_def, well_typed_custom_error_def, supported_pure_exprs_every,
     stmt_exprs_ok_flat, int_calls_stmt_def, int_calls_raise_reason_def, AllCaseEqs()] >>
  fs[EVERY_MEM, stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_raise_def] >>
  metis_tac[alloc_limits_expr_not_extcode, alloc_limits_exprs_mem]
QED

Theorem eval_assert_custom_bind:
  eval_stmt cx (Assert e (AssertCustomError err)) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. if v = BoolV T then return ()
           else if v = BoolV F then eval_stmt cx (Raise (RaiseCustomError err))
           else raise (Error (TypeError "not BoolV")))
Proof
  simp[FUN_EQ_THM, Once evaluate_def, eval_expr_switch_forced] >>
  gen_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx v st` >>
  Cases_on `read_result cx v st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[Once evaluate_def, bind_def]
QED

Theorem assert_custom_expr_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertCustomError err)))
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> pure_rewrite_tac[gas_admissible_def] >>
  rpt gen_tac >> disch_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `_ = (INR ex,ee)` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def] >> Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
     rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >>
     metis_tac[read_result_no_control, cj 1 eval_expr_no_control]) >>
  `eval_stmt cx (Assert e (AssertCustomError err)) (es with gas_obs := gs) =
    (INR ex,ee)` by simp[eval_assert_custom_bind, bind_def] >>
  drule_all gas_admissible_result >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

Theorem assert_custom_raise_admissible:
  gas_admissible (eval_stmt cx (Assert e (AssertCustomError err)))
    (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV F),mid with gas_obs := tail)) ==>
  gas_admissible (eval_stmt cx (Raise (RaiseCustomError err)))
    (stmt_res_ok lctx) (mid with gas_obs := [])
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `xs ++ gs` mp_tac) >>
  simp[eval_assert_custom_bind, bind_def] >> metis_tac[]
QED

Theorem type_stmt_assert_custom:
  type_stmt env ret_ty (Assert e (AssertCustomError err)) =
    (if well_typed_expr env e /\ well_typed_custom_error env err /\
        expr_type e = BaseT BoolT then SOME env else NONE)
Proof
  simp[Once type_stmt_def, CONJ_COMM]
QED

Theorem type_stmt_raise_custom[local]:
  type_stmt env ret_ty (Raise (RaiseCustomError err)) =
    (if well_typed_custom_error env err then SOME env else NONE)
Proof
  simp[Once type_stmt_def]
QED

Theorem supported_stmt_assert_custom[local]:
  supported_stmt tops bindings (Assert e (AssertCustomError err)) <=>
  supported_pure_expr tops e /\ supported_assert_reason tops (AssertCustomError err)
Proof
  simp[Once supported_stmt_def]
QED

Theorem supported_stmt_raise_custom[local]:
  supported_stmt tops bindings (Raise (RaiseCustomError err)) <=>
  supported_raise_reason tops (RaiseCustomError err)
Proof
  simp[Once supported_stmt_def]
QED

Theorem assert_custom_condition_bool:
  gas_admissible (eval_stmt cx (Assert e (AssertCustomError err))) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, mid with gas_obs := tail)) ==>
  ?b. v = BoolV b
Proof
  strip_tac >> spose_not_then assume_tac >>
  `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspecl_then [`xs`,
    `INR (Error (TypeError "not BoolV"))`, `mid with gas_obs := []`] mp_tac) >>
  simp[stmt_res_ok_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >> fs[] >>
  rewrite_tac[eval_assert_custom_bind] >>
  pure_once_rewrite_tac[bind_def] >> simp[raise_def]
QED

(* Only the actual condition trace can activate the conditional reason IH. *)
Theorem assert_custom_false_source_ready:
  expr_body_pre cenv cx env e es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  supported_stmt tops bindings (Assert e (AssertCustomError err)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e (AssertCustomError err)) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) =
       (INL (BoolV F), mid with gas_obs := tail)) ==>
expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  supported_stmt tops bindings (Raise (RaiseCustomError err)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Raise (RaiseCustomError err)) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env /\
  stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err)))
Proof
  strip_tac >>
  Cases_on `err` >>
  qpat_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >> fs[] >>
  `expr_body_pre cenv cx env e (es with gas_obs := xs)` by simp[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
  gvs[supported_stmt_assert_custom, supported_stmt_raise_custom,
      supported_assert_reason_def, supported_raise_reason_def,
      supported_stmt_expr_exists_def, supported_assert_exists_def,
      supported_raise_exists_def, type_stmt_assert_custom, type_stmt_raise_custom,
      stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_assert_def,
      alloc_limits_raise_def, int_calls_stmt_def, int_calls_raise_reason_def] >>
  simp[stmt_valued_return_def] >>
  gvs[int_calls_assert_reason_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED


Theorem assert_custom_condition_source_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assert e (AssertCustomError err)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e (AssertCustomError err)) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `supported_expr tops e` by
    (fs[supported_stmt_assert_custom] >> simp[supportedExprsTheory.supported_expr_def]) >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >> simp[supported_stmt_expr_exists_def]) >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module, body_inv_def] >>
  `well_typed_expr env e` by fs[type_stmt_assert_custom] >>
  drule_all_then strip_assume_tac bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
  `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `~is_extcode e` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      type_stmt_assert_custom, int_calls_stmt_def, body_inv_def] >>
  qexists_tac `int_calls_assert_reason (AssertCustomError err)` >> simp[]
QED

Theorem eval_raise_custom_non_normal:
  eval_stmt cx (Raise (RaiseCustomError err)) es = (res,ee) ==>
  res <> INL () /\ res <> INR BreakException /\ res <> INR ContinueException
Proof
  Cases_on `err` >>
  simp[Once evaluate_def] >>
  Cases_on `get_module_code cx (FST p)` >> simp[raise_def] >>
  rename1 `get_module_code cx _ = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops` >> simp[raise_def] >>
  rename1 `lookup_custom_error_args_in _ tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)` >>
  simp[raise_def, bind_def] >>
  rename1 `order_custom_error_args _ _ = SOME args` >>
  Cases_on `eval_exprs cx args es` >>
  Cases_on `q`
  >- (Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x` >>
      simp[bind_def, lift_option_def, raise_def, return_def] >> rpt strip_tac >> gvs[]) >>
  simp[bind_def] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 2 eval_expr_no_control) >> gvs[no_control_exc_def]
QED
