Theory bodyIfMemory
Ancestors
  allocLimits allocLimitsProps
  bodyExprPreFacts exprSimSource bodyMemoryPreds bodyMemoryDefs bodySim
  exprSimHypsDefs gasContext loweringPosts stmtSimDefs
  exprLoweringProps stmtLoweringProps stmtLoweringMono compileEnv
  supportedExprTraverse supportedStmtTraverse supportedStmts supportedExprs
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperInterpreter
  vyperTypeSystem vyperState vyperAST list finite_map
  stmtIfMemory

val _ = Parse.hide "body";

(* Former successful proof (before counted source-action schema):
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `!ty. expr_sim_mem ctx func cenv cx ty e es /\
        expr_vv_sim_mem ctx func cenv cx ty e es` by
    (gen_tac >>
     qpat_x_assum `body_expr_mem_ok _ _` (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then irule >> metis_tac[]) >>
  irule compile_if_stmt_frag_mem >> simp[stmts_env_cs_mono] >>
  reverse conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `?tv s1. eval_expr cx e es = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_mem_ok cx ss1 /\ body_stmts_mem_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (drule_all expr_body_pre_eval >> simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_mem_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_mem_ok_def])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED
*)
Theorem body_if_mem_case:
  !cx e ss1 ss2.
    (!s tv t s3 x t'.
       eval_expr cx e s = (INL tv,t) /\ push_scope s3 = (INL x,t') ==>
       body_stmts_mem_ok cx ss1) /\
    (!s tv t s3 x t'.
       eval_expr cx e s = (INL tv,t) /\ push_scope s3 = (INL x,t') ==>
       body_stmts_mem_ok cx ss2) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  fs[GSYM optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `!ty. expr_sim_mem ctx func cenv cx ty e es /\
        expr_vv_sim_mem ctx func cenv cx ty e es` by
    (gen_tac >>
     qpat_x_assum `body_expr_mem_ok _ _` (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then irule >> metis_tac[]) >>
  irule compile_if_stmt_frag_mem >> simp[stmts_env_cs_mono] >>
  conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `?tv s1. eval_expr cx e (es with gas_obs := gs) = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_mem_ok cx ss1 /\ body_stmts_mem_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (drule_all expr_body_pre_eval >> simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_mem_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_mem_ok_def, body_stmt_safe_def, body_stmts_safe_iff])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def,
      allocLimitsTheory.alloc_limits_stmt_def,
      compileVyperTheory.stmt_valued_return_def, GSYM optionTheory.IS_SOME_EXISTS] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

