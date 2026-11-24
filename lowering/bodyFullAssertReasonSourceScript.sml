(* Source boundaries for the full AssertReason case.  No reason execution
   or compiler implementation is duplicated here. *)
Theory bodyFullAssertReasonSource
Ancestors
  stateRelProj reasonSourceProps bodyFullPreds bodySimFull bodyExprPreFacts exprSimSource stmtSimReason
  bodySim allocLimits compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness
  gasOutcome gasContext stmtSimDefs supportedStmts supportedStmtTraverse
  vyperInterpreter vyperState vyperTypeSystem vyperAST list
  bodyInvCodeProps bodyInvSplit bodyInvMetadataProps exprSimHypsDefs exprBodyPreProps
  bodySingletonCallSupport compileUnit alist

Theorem type_stmt_assert_reason:
  type_stmt env ret_ty (Assert e (AssertReason r)) =
    (if well_typed_expr env e /\ well_typed_expr env r /\
        expr_type e = BaseT BoolT /\ (?n. expr_type r = BaseT (StringT n))
     then SOME env else NONE)
Proof
  simp[Once type_stmt_def]
QED

Theorem supported_stmt_assert_reason:
  supported_stmt tops bindings (Assert e (AssertReason r)) <=>
  supported_pure_expr tops e /\ supported_assert_reason tops (AssertReason r)
Proof
  simp[Once supported_stmt_def]
QED

Theorem assert_reason_condition_bool:
  gas_admissible (eval_stmt cx (Assert e (AssertReason r))) (stmt_res_ok lctx) es /\
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
  rewrite_tac[eval_assert_reason_bind] >>
  pure_once_rewrite_tac[bind_def] >> simp[raise_def]
QED

(* Only the actual condition trace can activate the conditional reason IH. *)
Theorem assert_reason_false_source_ready:
  (!s tv t. eval_expr cx e s = (INL tv,t) ==> body_expr_full_ok cx r) /\
  expr_body_pre cenv cx env e es /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  supported_stmt tops bindings (Assert e (AssertReason r)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e (AssertReason r)) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assert e (AssertReason r)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertReason r)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason r))) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) =
       (INL (BoolV F), mid with gas_obs := tail)) ==>
  body_expr_full_ok cx r /\
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  ce_locals_declared cenv env /\ locals_alloc_ok cenv env /\
  supported_stmt tops bindings (Raise (RaiseReason r)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Raise (RaiseReason r)) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Raise (RaiseReason r)) = SOME env /\
  stmt_exprs_ok cenv (Raise (RaiseReason r)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason r)))
Proof
  strip_tac >>
  qpat_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >> fs[] >>
  `expr_body_pre cenv cx env e (es with gas_obs := xs)` by simp[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
  `?tv t. eval_expr cx e (es with gas_obs := xs) = (INL tv,t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_full_ok cx r` by metis_tac[] >>
  gvs[supported_stmt_assert_reason, supported_stmt_raise_reason,
      supported_assert_reason_def, supported_raise_reason_def,
      supported_stmt_expr_exists_def, supported_assert_exists_def,
      supported_raise_exists_def, type_stmt_assert_reason, type_stmt_raise_reason,
      stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_assert_def,
      alloc_limits_raise_def, int_calls_stmt_def, int_calls_raise_reason_def] >>
  simp[stmt_valued_return_def] >>
  gvs[int_calls_assert_reason_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED


Theorem assert_reason_condition_source_pre_mods:
  contract_inv mods exps ctx cenv cx /\
  supported_stmt (main_module mods) bindings (Assert e (AssertReason r)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e (AssertReason r)) ==> occurs_abi_decode_target target (main_module mods)) /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (Assert e (AssertReason r)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertReason r)) /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason r))) ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  `supported_expr (main_module mods) e` by
    (fs[supported_stmt_assert_reason] >> simp[supportedExprsTheory.supported_expr_def]) >>
  `~supported_expr_exists (const_name_root_mods mods) e` by
    (drule_then assume_tac contract_inv_cenv_modules >>
     drule stmt_exprs_ok_module_const_name_free >>
     simp[supported_stmt_expr_exists_def]) >>
  `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `~is_extcode e` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
  mp_tac (Q.INST [`calls` |-> `int_calls_assert_reason (AssertReason r)`]
    stmt_expr_body_pre_main_mods) >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      type_stmt_assert_reason, int_calls_stmt_def]
QED

Theorem assert_reason_condition_source_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assert e (AssertReason r)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e (AssertReason r)) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assert e (AssertReason r)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertReason r)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason r))) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >> simp[supported_stmt_expr_exists_def]) >>
  drule_all_then assume_tac expr_sim_inv_no_unallocated_bare_globals >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by fs[expr_sim_inv_split_def] >>
  drule_all_then assume_tac
    (SIMP_RULE (srw_ss()) [main_module_def, ALOOKUP_def]
      (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`]
        assert_reason_condition_source_pre_mods)) >>
  drule_then assume_tac contract_inv_type_env >>
  fs[expr_body_pre_split_def, vyperContextTheory.type_env_all_modules_def,
     vyperContextTheory.type_env_def, finite_mapTheory.FUNION_FEMPTY_2,
     supported_stmt_expr_exists_def] >>
  `supported_expr tops e` by
    (fs[supported_stmt_assert_reason] >> simp[supportedExprsTheory.supported_expr_def]) >>
  metis_tac[bodySingletonCallSupportTheory.body_inv_typed_calls_main,
            expr_body_pre_mods_well_typed]
QED
