(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_log. *)
Theory bodyMemRawLog
Ancestors
  bodyMemoryPreds

Theorem body_raw_log_mem_case:
  !cx v20 es v21.
    body_exprs_mem_ok cx es ==> body_expr_mem_ok cx (Call v20 RawLog es v21)
Proof
  cheat
QED
