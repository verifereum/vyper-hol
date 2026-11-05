(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   selfdestruct. *)
Theory bodyMemSelfDestruct
Ancestors
  bodyMemoryPreds

Theorem body_selfdestruct_mem_case:
  !cx v24 es v25.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  cheat
QED
