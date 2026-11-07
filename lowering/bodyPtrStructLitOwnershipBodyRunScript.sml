Theory bodyPtrStructLitOwnershipBodyRun
Ancestors
  bodyPtrStructLitOwnershipStmtRecursion bodyPtrStructLitOwnershipShape
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFreshness
  loweringShapeProps loweringShapeDefs supportedStmtTraverse compileEnv stmtLowering

Theorem alloc_run_compile_stmts_shape_fresh:
  !ce lc ty body. ce.ce_alloca_locals /\ loop_ctx_shape_ok lc /\
  ~supported_stmts_expr_exists expr_shape_root body ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmts ce lc ty body) (\u s. shape_state s /\ fresh_outputs s)
Proof
  rpt strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any (cj 2 compile_stmt_shape) >>
  irule_at Any (cj 2 alloc_run_compile_stmt_route_mutual) >>
  simp[]
QED
