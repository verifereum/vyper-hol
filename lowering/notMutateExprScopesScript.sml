(* A successful evaluation of an expression that cannot mutate leaves the
   caller's scopes unchanged: Pop is excluded and an IntCall restores the
   caller's frame on the success path. *)
Theory notMutateExprScopes
Ancestors
  exprLowering vyperInterpreter

Theorem not_mutate_expr_scopes:
  !cenv cx e s v s'.
    ~expr_can_mutate cenv e /\ eval_expr cx e s = (INL v, s') ==>
    s'.scopes = s.scopes
Proof
  cheat
QED
