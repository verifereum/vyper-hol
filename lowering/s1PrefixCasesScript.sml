(* Request-prefix cases for the body induction. *)
Theory s1PrefixCases
Ancestors
  s1PrefixPreds s1PrefixReturnSome s1PrefixReturnNone s1PrefixExits
  allocLimits allocLimitsProps bodyExprPreFacts bodySim
  exprSimHypsDefs gasContext gasShadow supportedExprs supportedStmts
  supportedExprTraverse supportedStmtTraverse
  vyperAST vyperContext vyperInterpreter vyperTypeSystem vyperTypeCallGraph

Theorem body_return_case_prefix:
  !cx e.
    body_expr_full_ok cx e /\ body_expr_prefix_ok cx e ==>
    body_stmt_prefix_ok cx (Return (SOME e))
Proof
  rw[body_stmt_prefix_ok_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule (Q.SPECL [`cenv`, `cx`, `env`, `e`, `es`, `[]`]
              stmt_expr_body_pre) >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
         body_inv_def]
     >- (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
         qexists_tac `cenv` >>
         fs[alloc_limits_stmt_def, alloc_limits_expr_def]) >>
     metis_tac[]) >>
  irule compile_return_some_frag_prefix >>
  qpat_x_assum `body_expr_prefix_ok cx e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
    `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `ret_ty`, `es`] mp_tac) >>
  simp[]
QED

Theorem body_return_none_case_prefix:
  !cx. body_stmt_prefix_ok cx (Return NONE)
Proof
  simp[body_stmt_prefix_ok_def, gas_shadow_stmt_def,
       compile_return_none_frag_prefix]
QED

Theorem body_break_case_prefix:
  !cx. body_stmt_prefix_ok cx Break
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_continue_case_prefix:
  !cx. body_stmt_prefix_ok cx Continue
Proof
  simp[body_stmt_prefix_ok_def, compile_loop_jump_frag_prefix]
QED

Theorem body_raise_bare_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseBare)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED

Theorem body_raise_unreachable_case_prefix:
  !cx. body_stmt_prefix_ok cx (Raise RaiseUnreachable)
Proof
  simp[body_stmt_prefix_ok_def, compile_raise_frag_prefix]
QED
