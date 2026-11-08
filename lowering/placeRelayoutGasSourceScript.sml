Theory placeRelayoutGasSource
Ancestors
  placeRelayoutRawSource gasContext stmtSimDefs exprSimDefs
  vyperInterpreter vyperState vyperExprNoControl

Theorem assign_place_raw_rhs_admissible:
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!st pv ee. eval_expr cx e st = (INL pv,ee) ==> ?v. pv = Value v) ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res`
  >- (simp[expr_vv_res_ok_def] >> metis_tac[]) >>
  rename1 `INR ex` >>
  `no_control_exc ex` by metis_tac[cj 1 eval_expr_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl_tac [`ee`, `gs`] >>
     simp[Once evaluate_def, bind_def]) >>
  gvs[stmt_res_ok_def, expr_vv_res_ok_def, no_control_exc_def]
QED
