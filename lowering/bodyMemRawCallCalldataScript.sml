(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_call
   with calldata. *)
Theory bodyMemRawCallCalldata
Ancestors
  bodyMemoryPreds

Theorem body_raw_call_calldata_mem_case:
  !cx ty flags es v19.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED
