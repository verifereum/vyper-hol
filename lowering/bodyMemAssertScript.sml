(* Memory case of the body induction (bodyMemory's body_mem_mutual): bare and
   unreachable assert; stmtAssertMemory's compile_assert_frag_mem is the
   fragment step. *)
Theory bodyMemAssert
Ancestors
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
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag_mem >> gvs[type_stmt_def] >>
  fs[body_expr_mem_ok_def] >> metis_tac[compile_expr_grows]
QED
