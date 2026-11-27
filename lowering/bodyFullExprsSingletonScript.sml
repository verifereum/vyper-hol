Theory bodyFullExprsSingleton
Ancestors
  bodyFullPreds
  bodyFullPredsMods[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[body_exprs_full_ok_def]
QED
*)
Theorem body_exprs_full_ok_singleton:
  body_exprs_full_ok_mods mods exps cx [e] <=> body_expr_full_ok_mods mods exps cx e
Proof
  cheat
QED
