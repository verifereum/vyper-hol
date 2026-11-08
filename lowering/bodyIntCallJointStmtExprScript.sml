(* Raw expression statements discard their value without an emitted suffix. *)
Theory bodyIntCallJointStmtExpr
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtSeq stmtSimExpr bodySimStmtCases
  bodyExprPreFacts exprSimHypsDefs exprSimDefs exprSimSource loweringPosts
  stmtSimDefs stmtSimProps
  stmtLowering exprLowering exprLoweringProps compileEnv vyperInterpreter vyperState
  vyperTypeSystem vyperTypeCallStackSoundness supportedStmts supportedStmtTraverse
  supportedExprTraverse supportedExprs allocLimits gasOutcome gasSummary
  fragGasMode list finite_map bodySim vyperTypeCallGraph gasContext

Theorem intcall_stmts_producer_expr:
  !fp e. intcall_expr_producer fp e ==> intcall_stmts_producer fp [Expr e]
Proof
  rpt gen_tac >> strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >> strip_tac >> gvs[] >>
  `expr_body_pre ce fp.jc_cx env e es` by
    (irule stmt_expr_body_pre >>
     fs[intcall_joint_res_def, stmt_exprs_ok_def,
        supported_stmt_expr_exists_def, alloc_limits_stmt_def] >>
     drule supported_expr_body_calls >> strip_tac >>
     fs[body_inv_def, cx_tops_def, AllCaseEqs()] >>
     qexists_tac `[]` >> simp[call_evaluation_safe_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  qpat_x_assum `intcall_expr_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_expr_producer_def]) >>
  disch_then drule_all >> strip_tac >>
  pop_assum mp_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res ee r. _` strip_assume_tac >> gvs[]
      >- suspend "normal" >>
      suspend "exit") >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[expr_stmt_exempt]
QED

Resume intcall_stmts_producer_expr[normal]:
  qexistsl_tac [`INL ()`, `es_end`, `OK u`] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  `~is_HashMapRef tv` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     fs[] >> metis_tac[expr_stmt_not_hashmap]) >>
  conj_tac >- metis_tac[eval_expr_stmt_success] >>
  disj1_tac >>
  `~block_is_terminated sb` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     fs[] >>
     `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx` by
       fs[intcall_joint_res_def, stmt_state_rel_def, state_rel_def] >>
     `expr_body_pre ce fp.jc_cx env e
        (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
     drule_all compile_expr_open >> simp[]) >>
  gvs[intcall_expr_cont_def, stmt_lands_def, cenv_top_ext_refl,
      AllCaseEqs()]
QED

Resume intcall_stmts_producer_expr[exit]:
  Cases_on `res` >- fs[expr_exit_def] >>
  rename1 `INR ex` >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac
  >- (fs[gas_marked_exec_def] >> metis_tac[eval_expr_stmt_exception]) >>
  disj2_tac >> simp[intcall_stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise intcall_stmts_producer_expr
