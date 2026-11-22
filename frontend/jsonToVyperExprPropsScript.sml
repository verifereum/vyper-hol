Theory jsonToVyperExprProps
Ancestors
  jsonToVyperExpr vyperOriginFold vyperPinFoldProps vyperState

Theorem fold_pin_constant_eval_eq:
  eval_expr cx (fold_pin_constant e) st = eval_expr cx e st
Proof
  Cases_on `origin_fold_value e` >> simp[fold_pin_constant_def] >>
  drule origin_fold_value_literal_sound >>
  disch_then (qspecl_then [`st`, `cx`] SUBST1_TAC) >>
  simp[vyperInterpreterTheory.evaluate_def, return_def]
QED
