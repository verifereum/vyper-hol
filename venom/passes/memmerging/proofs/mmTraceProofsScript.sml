(* Reachability facts at the finite execution visits used by memmerging. *)
Theory mmTraceProofs
Ancestors
  dftGasFromListTraceDefs unitMemInv o1PassLift contextCodegenRelProps

Theorem mm_entry_trace_bound:
  reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn s /\
  fn_entry_state fn s /\
  (!i t. Inv ctx fn i t ==> static_mem_ok eom ctx fn i t) ==>
  EVERY (\((p,d,id),f,i,t).
    p = [] ==> static_mem_ok eom ctx f i t)
    (trace_function fuel ctx fn s)
Proof
  cheat
QED
