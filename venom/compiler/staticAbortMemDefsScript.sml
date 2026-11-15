(* Memory observations may precede an unavoidable static fault. *)
Theory staticAbortMemDefs
Ancestors
  staticAbortDefs unitMemInv venomState

Definition static_mem_ok_abort_def:
  static_mem_ok_abort eom ctx fn inst s <=>
    in_static_abort_prefix fn s \/ static_mem_ok eom ctx fn inst s
End

Theorem static_mem_ok_abort_nonstatic:
  ~s.vs_call_ctx.cc_static ==>
  (static_mem_ok_abort eom ctx fn inst s <=> static_mem_ok eom ctx fn inst s)
Proof
  simp[static_mem_ok_abort_def, in_static_abort_prefix_def]
QED
