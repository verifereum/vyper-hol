(* Ghost transport for the adopting oracle CALL endpoint. *)
Theory bodyFullExtCallCallGhost
Ancestors
  bodyFullExtCallGhost bodyFullExtCallFrames bodyFullUnwrapSlotPost
  bodyPtrDefs ptrDiscipline venomState venomInst finite_map pred_set

Theorem extcall_call_storage_ghost:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  stor_taint_ok_at D tn s /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_immutables = s.vs_immutables /\
  (~(inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
      u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
      (HD s.vs_outcomes).co_success) ==>
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient) ==>
  stor_taint_ok_at D (step_taint inst s u tn) u
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
    u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success` >>
  gvs[stor_taint_ok_at_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def] >> metis_tac[]
QED
