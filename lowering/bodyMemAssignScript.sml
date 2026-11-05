(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   assignment to a base target. *)
Theory bodyMemAssign
Ancestors
  bodyMemoryPreds

Theorem body_assign_mem_case:
  !cx t e.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==> body_base_target_mem_ok cx t) /\
    body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assign (BaseTarget t) e)
Proof
  cheat
QED
