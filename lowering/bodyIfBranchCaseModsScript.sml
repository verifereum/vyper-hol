(* Source entry for the selected arm of a linked If statement. *)
Theory bodyIfBranchCaseMods
Ancestors
  bodyFullPredsMods bodyBranchCellFrameMods bodyExprPreFacts
  bodyInvCodeProps bodyInvMetadataProps bodySim bodySimStmtFacts exprBodyPreProps
  supportedStmts supportedExprs supportedStmtTraverse supportedExprTraverse
  allocLimits allocLimitsProps vyperTypeSystem vyperTypeCallGraph
  vyperTypeInvariants vyperState

Theorem if_condition_pre_mods[local]:
  (!ctx cenv src tops env es bindings s ret_ty env'.
     contract_inv mods exps ctx cenv cx /\
     module_body_inv mods src tops cenv cx /\
     expr_sim_inv_mods mods cenv cx env es /\
     body_const_cells_agree_mods mods cx env es /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  supported_stmt tops bindings (If e yes no) /\
  type_stmt env ret_ty (If e yes no) = SOME env' /\
  stmt_exprs_ok cenv (If e yes no) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (If e yes no) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (If e yes no) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (If e yes no)) ==>
  expr_type e = BaseT BoolT /\ expr_body_pre_mods mods cenv cx env e es
Proof
  disch_then (mk_asm "resolve") >> strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (If e yes no))` by
    (asm "resolve" irule >> metis_tac[]) >>
  asm_x "resolve" kall_tac >>
  `well_typed_expr env e /\ expr_type e = BaseT BoolT` by
    fs[type_stmt_def, AllCaseEqs()] >>
  `supported_expr tops e` by fs[Once supported_stmt_def, supported_expr_def] >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  drule_then assume_tac (cj 1 alloc_limits_expr_exists) >>
  simp[] >>
  irule (Q.INST [`calls` |-> `int_calls_stmts yes ++ int_calls_stmts no`]
    (SPEC_ALL stmt_expr_body_pre_mods)) >>
  fs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def,
     DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj] >>
  qexistsl_tac [`no`, `yes`] >> simp[]
QED
