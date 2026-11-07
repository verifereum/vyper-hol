(* Memory case of the body induction (bodyMemory's body_mem_mutual): a
   ternary. bodyExprClosureMemory's body_ifexp_word_mem_case (with
   bodyIfExpMemory) predates the gas-counted expr_sim_mem and needs porting;
   non-word ternaries have no case yet. *)
Theory bodyMemIfExp
Ancestors
  bodyMemoryPreds

Theorem body_ifexp_mem_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_mem_ok cx e3) /\
    body_expr_mem_ok cx e1 ==>
    body_expr_mem_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED
