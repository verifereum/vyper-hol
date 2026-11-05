(* Memory case of the body induction (bodyMemory's body_mem_mutual): an if
   statement. bodyIfMemory's body_if_mem_case is this case but predates the
   gas-counted stmt_frag_mem and fails; port it (stmtIfMemory's
   compile_if_stmt_frag_mem builds). *)
Theory bodyMemIf
Ancestors
  bodyMemoryPreds

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
  cheat
QED
