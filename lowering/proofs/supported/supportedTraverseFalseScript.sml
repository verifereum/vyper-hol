Theory supportedTraverseFalse
Ancestors
  supportedExprTraverse

Theorem supported_exists_false:
  (!e. ~supported_expr_exists (\x. F) e) /\
  (!t. ~supported_target_exists (\x. F) t) /\
  (!es. ~supported_exprs_exists (\x. F) es)
Proof
  `(!p e. p = (\x. F) ==> ~supported_expr_exists p e) /\
   (!p t. p = (\x. F) ==> ~supported_target_exists p t) /\
   (!p es. p = (\x. F) ==> ~supported_exprs_exists p es) /\
   (!p opt. p = (\x. F) ==> ~supported_opt_exists p opt) /\
   (!p fields. p = (\x. F) ==> ~supported_fields_exists p fields)` by
    (ho_match_mp_tac supported_expr_exists_ind >>
     rw[supported_expr_exists_def]) >>
  simp[]
QED
