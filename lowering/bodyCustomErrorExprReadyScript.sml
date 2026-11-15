(* Argument interfaces for custom-error statement composition. *)
Theory bodyCustomErrorExprReady
Ancestors
  bodySimExprCases bodyExprPreFacts exprSimSource supportedExprTraverse
  supportedStmtTraverse supportedExprs vyperTypeSystem vyperTypeContract
  bodyCustomErrorSource bodySim gasContext vyperTypeCallGraph

(* body_exprs_ok_case already supplies exprs_case; no duplicate adapter. *)
Theorem custom_error_raise_args_well_typed:
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' ==>
  well_typed_exprs env (custom_error_exprs err)
Proof
  Cases_on `err` >> simp[type_stmt_def, well_typed_custom_error_def,
    AllCaseEqs()] >> metis_tac[]
QED

Theorem custom_error_raise_arg_body_pre:
  body_inv tops ctx ce cx /\
  EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
  stmt_exprs_ok ce (Raise (RaiseCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Raise (RaiseCustomError err)) ==> occurs_abi_decode_target target tops) ==>
  !e ee. MEM e (custom_error_exprs err) /\ expr_sim_inv ce cx env ee ==>
    expr_body_pre ce cx env e ee
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `supported_pure_expr tops e` by fs[listTheory.EVERY_MEM] >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  `well_typed_expr env e` by
    metis_tac[custom_error_raise_args_well_typed, well_typed_exprs_member] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
  irule stmt_expr_body_pre >> simp[] >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_raise_exists_def, supported_exprs_exists_every,
      listTheory.EXISTS_MEM, int_calls_stmt_def, int_calls_raise_reason_def] >>
  rpt conj_tac
  >- (fs[body_inv_def] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[] >>
  qexists_tac `int_calls_exprs (custom_error_exprs err)` >> simp[]
QED
