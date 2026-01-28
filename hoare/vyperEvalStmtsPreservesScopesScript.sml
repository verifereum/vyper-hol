Theory vyperEvalStmtsPreservesScopes

Ancestors
  vyperInterpreter vyperLookup vyperEvalExprPreservesScopeDom vyperScopePreservationLemmas

(***)

Theorem eval_stmts_preserves_scopes:
  ∀cx st st' ss res.
    eval_stmts cx ss st = (res, st') ⇒
    (FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
     MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes))
Proof
  cheat
QED
