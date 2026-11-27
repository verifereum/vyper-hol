Theory bodyFullExprsSingleton
Ancestors
  bodyFullPreds

Theorem body_exprs_full_ok_singleton:
  body_exprs_full_ok cx [e] <=> body_expr_full_ok cx e
Proof
  simp[body_exprs_full_ok_def]
QED
