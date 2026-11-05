(* Memory case of the body induction (bodyMemory's body_mem_mutual): send. *)
Theory bodyMemSend
Ancestors
  bodyMemoryPreds

Theorem body_send_mem_case:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Call v12 (Send has_gas) es v13)
Proof
  cheat
QED
