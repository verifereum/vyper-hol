(* Memory case of the body induction (bodyMemory's body_mem_mutual): append. *)
Theory bodyMemAppend
Ancestors
  bodyMemoryPreds

Theorem body_append_mem_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t ==>
    body_stmt_mem_ok cx (Append t e)
Proof
  cheat
QED
