(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   subscript. *)
Theory bodyMemSubscript
Ancestors
  bodyMemoryPreds

Theorem body_subscript_mem_case:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_mem_ok cx e2) /\
    body_expr_mem_ok cx e1 ==>
    body_expr_mem_ok cx (Subscript v8 e1 e2)
Proof
  cheat
QED
