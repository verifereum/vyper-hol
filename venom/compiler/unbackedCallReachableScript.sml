(* An exhausted-oracle call at the boundary of a guarded history. *)
Theory unbackedCallReachable
Ancestors
  guardedFrameReachable

Definition unbacked_call_reachable_def:
  unbacked_call_reachable ctx vs <=>
    ?fn inst s fuel post.
      guarded_raw_reachable vs ctx fn inst s /\
      active_inst fn inst s /\
      MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
      s.vs_outcomes = [] /\
      step_inst fuel ctx inst s = OK post
End
