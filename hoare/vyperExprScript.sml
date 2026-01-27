Theory vyperExpr

(* Theorems about expression evaluation.
 *)

Ancestors
  vyperInterpreter vyperScopes

Theorem eval_expr_preserves_scopes:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  cheat
QED
