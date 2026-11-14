(* A straight static-fault prefix cannot leave its block normally. *)
Theory staticAbortExec
Ancestors
  staticAbortDefs venomExecProofs venomExecSemantics venomInstProofs
  venomState venomInst opcodeClass list

(* Successful intermediate steps preserve the static flag. The pending
   storage/log write either faults statically or has invalid operands. *)
Theorem static_abort_at_no_normal:
  s.vs_call_ctx.cc_static /\ static_abort_at bb s.vs_inst_idx ==>
  exec_block fuel ctx bb s <> OK t /\
  exec_block fuel ctx bb s <> IntRet ret t
Proof
  simp[static_abort_at_def]
QED
