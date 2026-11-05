(* Memory case of the body induction (bodyMemory's body_mem_mutual): assert
   with a reason string. *)
Theory bodyMemAssertReason
Ancestors
  bodyMemoryPreds

Theorem body_assert_reason_mem_case:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_mem_ok cx se) /\
    body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED
