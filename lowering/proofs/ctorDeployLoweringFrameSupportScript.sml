Theory ctorDeployLoweringFrameSupport
Ancestors
  supportedStmts supportedExprTraverse supportedExprs supportedExprForms
  supportedTargets supportedStmtTraverse exprLowering allocLimits vyperAST

Theorem deploy_frame_expr_exists_disj:
  (!p e q. supported_expr_exists (\x. p x \/ q x) e <=>
    supported_expr_exists p e \/ supported_expr_exists q e) /\
  (!p t q. supported_target_exists (\x. p x \/ q x) t <=>
    supported_target_exists p t \/ supported_target_exists q t) /\
  (!p es q. supported_exprs_exists (\x. p x \/ q x) es <=>
    supported_exprs_exists p es \/ supported_exprs_exists q es) /\
  (!p oe q. supported_opt_exists (\x. p x \/ q x) oe <=>
    supported_opt_exists p oe \/ supported_opt_exists q oe) /\
  (!p fs q. supported_fields_exists (\x. p x \/ q x) fs <=>
    supported_fields_exists p fs \/ supported_fields_exists q fs)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  simp[supported_expr_exists_def] >> metis_tac[]
QED

Theorem deploy_frame_assignment_exists_disj:
  (!p t q. supported_assignment_exists (\x. p x \/ q x) t <=>
    supported_assignment_exists p t \/ supported_assignment_exists q t) /\
  (!p ts q. supported_assignments_exists (\x. p x \/ q x) ts <=>
    supported_assignments_exists p ts \/ supported_assignments_exists q ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  simp[supported_assignment_exists_def, deploy_frame_expr_exists_disj] >> metis_tac[]
QED

Theorem deploy_frame_stmt_exists_disj:
  (!p s q. supported_stmt_expr_exists (\x. p x \/ q x) s <=>
    supported_stmt_expr_exists p s \/ supported_stmt_expr_exists q s) /\
  (!p ss q. supported_stmts_expr_exists (\x. p x \/ q x) ss <=>
    supported_stmts_expr_exists p ss \/ supported_stmts_expr_exists q ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  simp[supported_stmt_expr_exists_def, deploy_frame_expr_exists_disj,
       deploy_frame_assignment_exists_disj] >>
  rpt conj_tac >> rpt gen_tac >>
  all_tac >~ [`supported_assert_exists _ reason`]
  >- (Cases_on `reason` >>
      simp[supported_assert_exists_def, GSYM supported_exprs_exists_every,
           deploy_frame_expr_exists_disj] >> metis_tac[]) >>
  all_tac >~ [`supported_raise_exists _ reason`]
  >- (Cases_on `reason` >>
      simp[supported_raise_exists_def, GSYM supported_exprs_exists_every,
           deploy_frame_expr_exists_disj]) >>
  all_tac >~ [`supported_iterator_exists _ iter`]
  >- (Cases_on `iter` >>
      simp[supported_iterator_exists_def, deploy_frame_expr_exists_disj] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem deploy_frame_remove_extcode_guard:
  ~supported_stmts_expr_exists is_extcode ss /\
  ~supported_stmts_expr_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) ss ==>
  ~supported_stmts_expr_exists (\e. ~alloc_limits_expr cenv e) ss
Proof
  `(!e. is_extcode e \/ (~is_extcode e /\ ~alloc_limits_expr cenv e) <=>
         is_extcode e \/ ~alloc_limits_expr cenv e)` by metis_tac[] >>
  `supported_stmts_expr_exists
     (\e. is_extcode e \/ (~is_extcode e /\ ~alloc_limits_expr cenv e)) ss =
   supported_stmts_expr_exists
     (\e. is_extcode e \/ ~alloc_limits_expr cenv e) ss` by
    (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]) >>
  gvs[deploy_frame_stmt_exists_disj] >> metis_tac[]
QED
