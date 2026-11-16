(* Source boundaries for the full AssertReason case.  No reason execution
   or compiler implementation is duplicated here. *)
Theory bodyFullAssertReasonSource
Ancestors
  reasonSourceProps bodyFullPreds bodySimFull bodyExprPreFacts exprSimSource stmtSimReason
  bodySim allocLimits compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness
  gasOutcome gasContext stmtSimDefs supportedStmts supportedStmtTraverse
  vyperInterpreter vyperState vyperTypeSystem vyperAST list

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
  expr_sim_pre cenv cx env e es /\
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
  `expr_sim_pre cenv cx env e (es with gas_obs := xs)` by simp[] >>
  qpat_x_assum `expr_sim_pre _ _ _ _ es` kall_tac >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[expr_sim_pre_eval] >>
  `?tv t. eval_expr cx e (es with gas_obs := xs) = (INL tv,t)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_expr_full_ok cx r` by metis_tac[] >>
  gvs[supported_stmt_def, supported_assert_reason_def, supported_raise_reason_def,
      supported_stmt_expr_exists_def, supported_assert_exists_def,
      supported_raise_exists_def, type_stmt_def,
      stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_assert_def,
      alloc_limits_raise_def, int_calls_stmt_def, int_calls_raise_reason_def] >>
  simp[stmt_valued_return_def] >>
  gvs[int_calls_assert_reason_def] >>
  metis_tac[call_evaluation_safe_append_right]
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
  expr_sim_pre cenv cx env e es
Proof
  strip_tac >>
  `supported_pure_expr tops e /\ supported_expr tops e /\ int_calls_expr e = []` by
    (gvs[supported_stmt_def, supported_assert_reason_def] >>
     metis_tac[supported_pure_int_calls, supportedExprsTheory.supported_expr_def]) >>
  `~supported_expr_exists (const_name_root cx) e` by
    metis_tac[bodySimTheory.body_inv_const_name_free] >>
  simp[expr_sim_pre_body] >> irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_assert_exists_def, type_stmt_def, int_calls_stmt_def,
      body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  drule supported_expr_body_calls >> strip_tac >> gvs[] >> metis_tac[]
QED
