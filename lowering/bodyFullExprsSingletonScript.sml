Theory bodyFullExprsSingleton
Ancestors
  bodyFullPreds
  bodyFullPredsMods[qualified]

Theorem body_exprs_full_ok_singleton:
  !mods exps.
  body_exprs_full_ok_mods mods exps cx [e] <=> body_expr_full_ok_mods mods exps cx e
Proof
  simp[body_exprs_full_ok_def]
QED
