Theory bodyPtrStructLitOwnershipStmtCases
Ancestors bodyPtrStructLitOwnershipStmtHelpers bodyPtrStructLitOwnershipRecursion
  bodyPtrStructLitOwnershipDeclarationRoute bodyPtrStructLitAssignFrame
  stmtLowering loweringShapeProps supportedExprTraverse compileEnv
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitCompilerOwnership loweringShapeDefs loweringShapeRules
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops

Theorem alloc_run_stmt_nonannassign_route:
  (!id vt e. s <> AnnAssign id vt e) /\
  alloc_run P (compile_stmt ce lctx ty s) Q ==>
  alloc_run P
    (comp_bind (declare_stmt_local ce s) (\ce'. compile_stmt ce' lctx ty s)) Q
Proof
  strip_tac >> simp[alloc_run_def, comp_bind_def] >> rpt strip_tac >>
  Cases_on `declare_stmt_local ce s st` >> gvs[] >>
  drule_all declare_stmt_local_nonannassign_identity >> strip_tac >> gvs[] >>
  gvs[alloc_run_def] >> metis_tac[]
QED

Theorem alloc_run_stmt_pass:
  alloc_run (\st. T) (compile_stmt ce lctx ty Pass) (\u st. T)
Proof simp[compile_stmt_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_expr:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (compile_stmt ce lctx ty (Expr e)) (\u st. T)
Proof
  strip_tac >> simp[compile_stmt_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v st. T` >> reverse conj_tac
  >- simp[alloc_run_compile_expr] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_stmt_lower_value:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce)
    (lower_value compile_expr ce ty e)
    (\v st. shape_state st /\ cenv_shape_ok st ce)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`R` |-> `\s. T`] alloc_run_lower_value_frame) >>
  simp[shape_stable_def, alloc_run_compile_expr, cj 1 compile_expr_shape]
QED

Theorem alloc_run_stmt_raise_simple:
  alloc_run fresh_outputs (compile_stmt ce lctx ty (Raise RaiseBare))
    (\u st. fresh_outputs st) /\
  alloc_run fresh_outputs (compile_stmt ce lctx ty (Raise RaiseUnreachable))
    (\u st. fresh_outputs st)
Proof
  simp[compile_stmt_def, alloc_run_emit_empty_fresh]
QED

