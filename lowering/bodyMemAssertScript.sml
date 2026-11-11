(* Memory case of the body induction (bodyMemory's body_mem_mutual): bare and
   unreachable assert; stmtAssertMemory's compile_assert_frag_mem is the
   fragment step. *)
Theory bodyMemAssert
Ancestors
  supportedExprTraverse allocLimits
  bodyMemoryPreds stmtAssertMemory bodyExprPreFacts exprLoweringProps
  bodySim supportedStmtTraverse supportedStmts vyperTypeCallGraph
  vyperTypeSystem allocLimitsProps gasContext

Theorem body_assert_mem_case:
  !cx e ak.
    (ak = AssertBare \/ ak = AssertUnreachable) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assert e ak)
Proof
  rw[body_stmt_mem_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supportedExprsTheory.supported_expr_def] >>
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
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag_mem >> gvs[type_stmt_def] >>
  fs[body_expr_mem_ok_def] >> metis_tac[compile_expr_grows]
QED
