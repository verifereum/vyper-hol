(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_call
   to a target. *)
Theory bodyMemRawCall
Ancestors
  bodyMemoryPreds bodyMemRawCallRevert bodyMemRawCallBounds bodyMemRawCallFinish
  rawCallFinishPathMemory rawCallTupleMemory

Theorem body_raw_call_mem_case:
  !cx ty flags es v18.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  cheat
QED
