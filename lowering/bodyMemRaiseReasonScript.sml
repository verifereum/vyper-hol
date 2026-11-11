(* Memory case of the body induction (bodyMemory's body_mem_mutual): raise
   with a reason string.  A string literal goes to stmtReasonLitFragMemory;
   any other reason through its value_vv (stmtReasonVvMemory) to the revert
   path of its kind (stmtReasonKindsMemory). *)
Theory bodyMemRaiseReason
Ancestors
  allocLimitsProps
  bodyMemoryPreds stmtReasonLitFragMemory stmtReasonVvMemory
  stmtReasonKindsMemory bodyExprPreFacts bodySim supportedStmtTraverse
  supportedExprTraverse supportedStmts vyperTypeSystem exprSimHyps
  allocLimits gasContext vyperAST vyperTypeCallGraph compileEnv exprLoweringProps

Theorem body_raise_reason_mem_case:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Raise (RaiseReason e))
Proof
  rw[body_stmt_mem_ok_def] >>
  `supported_string_reason tops e` by
    gvs[supported_stmt_def, supported_raise_reason_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  `~is_extcode e` by
    (irule alloc_limits_expr_not_extcode >>
     fs[stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_raise_def]) >>
  `~supported_expr_exists
      (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) e` by
    gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
        supported_raise_exists_def] >>
  `alloc_limits_expr cenv e` by
    (CCONTR_TAC >> qpat_x_assum `~supported_expr_exists _ _` mp_tac >>
     simp[] >> irule supported_expr_exists_root >> fs[]) >>
  Cases_on `?ml str. e = Literal (BaseT (StringT ml)) (StringL str)`
  >- (gvs[] >> irule compile_raise_reason_lit_frag_mem >>
      gvs[well_typed_expr_def, well_typed_literal_def] >>
      drule alloc_limits_expr_type_alloc_ok >>
      simp[type_alloc_ok_def, expr_type_def, is_word_type_def]) >>
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
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_raise_exists_def, int_calls_stmt_def,
         int_calls_raise_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_mem ctx func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_mem_ok_def] >>
  irule compile_raise_reason_vv_frag_mem >> fs[] >>
  rpt strip_tac >> metis_tac[reason_revert_path_mem]
QED
