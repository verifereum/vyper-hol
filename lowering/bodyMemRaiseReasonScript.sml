(* Memory case of the body induction (bodyMemory's body_mem_mutual): raise
   with a reason string. *)
Theory bodyMemRaiseReason
Ancestors
  bodyMemoryPreds

Theorem body_raise_reason_mem_case:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED
