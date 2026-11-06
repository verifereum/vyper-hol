(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   raw_revert. *)
Theory bodyMemRawRevert
Ancestors
  bodyMemoryPreds

Theorem body_raw_revert_mem_case:
  !cx v22 es v23.
    body_exprs_mem_ok cx es ==> body_expr_mem_ok cx (Call v22 RawRevert es v23)
Proof
  cheat
QED
