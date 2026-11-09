(* Source typing at a counted materialized-child endpoint. *)
Theory bodyIntCallFamAggStructSource
Ancestors
  bodyIntCallFamAggStructFields exprSimAggregateSource exprSimSource
  vyperState gasSummary

Theorem gas_marked_materialised_child_wf:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s) marks (INL v) mid r
  ==> val_wf tv v
Proof
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  simp[bind_def] >>
  Cases_on `eval_expr cx e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings)` >>
  rename1 `eval_expr _ _ _ = (res,ee)` >>
  Cases_on `res` >> simp[] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  irule aggregate_materialised_child_wf >>
  metis_tac[expr_body_pre_gas_obs]
QED
