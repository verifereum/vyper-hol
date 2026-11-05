(* Memory case of the body induction (bodyMemory's body_mem_mutual): an if
   statement, which is bodyIfMemory's body_if_mem_case. *)
Theory bodyMemIf
Ancestors
  bodyMemoryPreds bodyIfMemory

Theorem body_if_mem_ok:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_mem_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_mem_ok cx ss2) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (If e ss1 ss2)
Proof
  ACCEPT_TAC body_if_mem_case
QED
