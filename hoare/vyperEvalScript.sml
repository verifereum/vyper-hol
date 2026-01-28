Theory vyperEval

Ancestors
  vyperInterpreter vyperScopes vyperExpr vyperLookup

Theorem eval_expr_preserves_var_in_scope:
  ∀cx st st' n e v. var_in_scope st n ∧ eval_expr cx e st = (INL v, st') ⇒ var_in_scope st' n
Proof
  metis_tac[var_in_scope_dom_iff, eval_expr_preserves_scopes_dom]
QED
