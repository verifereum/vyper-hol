(* Raise reasons from the joint value producer. *)
Theory bodyIntCallFamStmtExitRaise
Ancestors
  bodyIntCallFamStmtExitBoundary bodyIntCallFamStmtExitLiteral
  bodyIntCallJointContract bodyIntCallJointStmtSeq bodyIntCallJointStmtRaise
  stmtReasonVvMemory stmtSimReasonExpr bodySimStmtCases bodyExprPreFacts exprSimHypsDefs
  exprSimDefs exprSimSource loweringPosts stmtSimDefs stmtSimProps
  stmtLowering exprLowering exprLoweringProps compileEnv vyperInterpreter vyperState
  vyperTypeSystem vyperTypeCallStackSoundness supportedStmts supportedStmtTraverse
  supportedExprTraverse supportedExprs allocLimits gasOutcome gasSummary
  fragGasMode fragGasPath fragExec list finite_map bodySim vyperTypeCallGraph gasContext
Libs monadsyntax

Theorem intcall_stmts_producer_raise_reason:
  intcall_expr_producer fp e ==>
  intcall_stmts_producer fp [Raise (RaiseReason e)]
Proof
  strip_tac >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule intcall_stmts_producer_raise_literal) >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, supported_raise_reason_def,
      supported_raise_exists_def, int_calls_raise_reason_def] >>
  `supported_expr fp.jc_tops e` by
    (Cases_on `e` >>
     gvs[supported_string_reason_def, supported_expr_def,
         supported_pure_expr_def, AllCaseEqs()]) >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, compile_reason_message_expr,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  suspend "setup"
QED

Resume intcall_stmts_producer_raise_reason[setup]:
  pairarg_tac >> gvs[AllCaseEqs()] >>
  rename1 `compile_expr ce _ e sa = (msg_op,reason_cs)` >>
  rename1 `compile_revert_with_reason ce msg_op _ _ reason_cs = ((),abort_cs)` >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (irule stmt_expr_body_pre >>
     fs[intcall_joint_res_def, stmt_exprs_ok_def,
        supported_stmt_expr_exists_def, supported_raise_exists_def,
        alloc_limits_stmt_def] >>
     drule supported_expr_body_calls >> strip_tac >>
     fs[body_inv_def, cx_tops_def, AllCaseEqs()] >>
     qexists_tac `[]` >> simp[call_evaluation_safe_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[raise_reason_expr_admissible] >>
  `cs_extends sa reason_cs` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends reason_cs abort_cs` by metis_tac[revert_reason_grows] >>
  `fn_has_code sa reason_cs fp.jc_func /\ fn_has_code reason_cs abort_cs fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  qpat_x_assum `intcall_expr_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_expr_producer_def]) >>
  disch_then drule_all >> strip_tac >>
  pop_assum mp_tac >> simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res ee r. _` strip_assume_tac >> gvs[]
      >- suspend "normal" >> suspend "exit") >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[raise_reason_exempt]
QED

Resume intcall_stmts_producer_raise_reason[exit]:
  Cases_on `res` >- fs[expr_exit_def] >>
  rename1 `expr_exit (INR ex) r` >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac
  >- (fs[gas_marked_exec_def] >> gen_tac >>
      asm_simp_tac (srw_ss()) [eval_raise_reason_eq] >> simp[Once bind_def]) >>
  disj2_tac >> simp[intcall_stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume intcall_stmts_producer_raise_reason[normal]:
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa reason_cs s
     (es_end with gas_obs := []) tv msg_op u` by
    (irule intcall_expr_endpoint_vv_post >>
     simp[vv_storage_live_gas_obs] >>
     qexists_tac `env` >> simp[]) >>
  drule vv_post_read_ok >> strip_tac >>
  `reason_vv_ok msg_op \/ reason_storage_vv msg_op \/ reason_code_vv msg_op` by
    (fs[intcall_joint_res_def] >>
     metis_tac[supported_reason_encoder_shape]) >>
  (`?t. gas_path fp.jc_ctx fp.jc_func u 0 (Abort Revert_abort t)` by
    (fs[intcall_expr_cont_def] >>
     metis_tac[intcall_reason_abort_path]) >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
  drule_all raise_reason_read_string >> strip_tac >> gvs[] >>
  qexistsl_tac [`INR (AssertException str)`, `es_end`, `Abort Revert_abort t`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def] >> conj_tac
      >- (irule raise_reason_source >> goal_assum (drule_at Any) >> simp[]) >>
      metis_tac[gas_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  simp[exit_result_def, intcall_stmt_exit_def, expr_exit_def])
QED

Finalise intcall_stmts_producer_raise_reason
