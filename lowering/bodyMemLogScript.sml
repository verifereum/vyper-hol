(* Memory case of the body induction (bodyMemory's body_mem_mutual): log. *)
Theory bodyMemLog
Ancestors
  bodyMemoryPreds

Theorem body_log_mem_case:
  !cx id es. body_exprs_mem_ok cx es ==> body_stmt_mem_ok cx (Log id es)
Proof
  cheat
QED
