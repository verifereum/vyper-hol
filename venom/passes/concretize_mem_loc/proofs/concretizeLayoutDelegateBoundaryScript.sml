Theory concretizeLayoutDelegateBoundary
Ancestors concretizeLayoutReaderContext concretizeLayoutExternalRequests
  frameRelocationEnvironment venomExecSemantics ptrDiscipline

(* A clean DELEGATECALL sees identical account and transient snapshots, so
   both runs send the same request to the CALL outcome oracle. *)
Theorem concretize_delegate_clean_snapshots:
  concretize_supplement D tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = DELEGATECALL ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >> irule concretize_supplement_clean_accounts >>
  gvs[taint_ok_def] >> metis_tac[]
QED
