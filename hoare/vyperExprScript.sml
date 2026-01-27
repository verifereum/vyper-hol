Theory vyperExpr

(* Theorems about expression evaluation.
 *)

Ancestors
  vyperInterpreter vyperScopes

(* Pure expressions: expressions that do not modify scopes.
   Pop is the only impure expression constructor - it modifies scoped variables.
*)

Definition pure_expr_def:
  pure_expr (Name _) = T ∧
  pure_expr (TopLevelName _) = T ∧
  pure_expr (FlagMember _ _) = T ∧
  pure_expr (Literal _) = T ∧
  pure_expr (IfExp e1 e2 e3) = (pure_expr e1 ∧ pure_expr e2 ∧ pure_expr e3) ∧
  pure_expr (StructLit _ kes) = EVERY pure_expr (MAP SND kes) ∧
  pure_expr (Subscript e1 e2) = (pure_expr e1 ∧ pure_expr e2) ∧
  pure_expr (Attribute e _) = pure_expr e ∧
  pure_expr (Builtin _ es) = EVERY pure_expr es ∧
  pure_expr (TypeBuiltin _ _ es) = EVERY pure_expr es ∧
  pure_expr (Pop _) = F ∧
  pure_expr (Call _ es) = EVERY pure_expr es
Termination
  WF_REL_TAC `measure expr_size` >>
  rw[] >>
  Induct_on `kes` >> rw[] >>
  PairCases_on `h` >> rw[] >>
  res_tac >> simp[]
End

Theorem eval_expr_preserves_scopes:
  ∀cx e st res st'.
    pure_expr e ∧ eval_expr cx e st = (res, st') ⇒
    st.scopes = st'.scopes
Proof
  cheat
QED

Theorem eval_expr_preserves_scopes_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  cheat
QED
