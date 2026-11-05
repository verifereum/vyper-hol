Theory bodyPtrPopCallTaintBoundary
Ancestors
  bodyPtrPopSavedTransport bodyPtrDefs ptrDiscipline venomInst venomState
  pred_set

(* An adopting CALL resets storage taint irrespective of the shape of a
   saved region. This is an operational boundary, not an index frame theorem. *)
Theorem pop_adopting_call_storage_taint:
  inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
  s'.vs_requests <> s.vs_requests /\
  s'.vs_outcomes <> s.vs_outcomes /\
  (HD s.vs_outcomes).co_success ==>
  (step_taint inst s s' tn).t_stor = {} /\
  (step_taint inst s s' tn).t_trans = {}
Proof
  simp[step_taint_def, adopt_reset_def]
QED

(* In particular, the storage part of ptr_vv_ok does not require that a
   saved child is still globally live, canonical, or within its capacity. *)
Theorem pop_clean_storage_place_ptr:
  op_taint tn p.ptr_operand = {} /\
  ((p.ptr_location = LocStorage /\ tn.t_stor = {}) \/
   (p.ptr_location = LocTransient /\ tn.t_trans = {})) ==>
  ptr_vv_ok cx t result (LocatedValue t' p) es G tn s
Proof
  strip_tac >> simp[ptr_vv_ok_def]
QED
