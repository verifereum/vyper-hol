(* Typed operand boundary for account builtin pointer consumers. *)
Theory bodyPtrEnvBuiltinsAccounts
Ancestors
  bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsCodeProbe
  bodyPtrEnvBuiltinsScalarCompose exprSimAccounts exprSimHypsDefs
  vyperTyping vyperTypeSystem vyperAST list exprOpenFirstOperand

Theorem account_body_pre_args:
  expr_body_pre cenv cx env (Builtin ann (Acc item) args) es ==>
  ?e. args = [e] /\ ann = account_item_type item /\
      expr_type e = BaseT AddressT /\ expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `?e. args = [e] /\ ann = account_item_type item /\
       expr_type e = BaseT AddressT` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >> irule expr_body_pre_builtin_head >>
  goal_assum (drule_at Any) >> simp[]
QED
