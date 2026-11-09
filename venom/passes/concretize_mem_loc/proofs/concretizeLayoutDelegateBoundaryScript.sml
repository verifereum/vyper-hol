Theory concretizeLayoutDelegateBoundary
Ancestors concretizeLayoutReaderContext concretizeLayoutExternalRequests
  frameRelocationEnvironment venomExecSemantics ptrDiscipline

(* Concrete delegate execution observes identical EVM inputs, rather than
   consuming the CALL outcome oracle. *)
Theorem concretize_delegate_input:
  relocation_reader_context s t /\ s.vs_call_ctx = t.vs_call_ctx /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient ==>
  make_venom_delegatecall_state s target gas calldata code is_static =
  make_venom_delegatecall_state t target gas calldata code is_static
Proof
  strip_tac >> drule relocation_reader_context_tx_params >>
  simp[make_venom_delegatecall_state_def]
QED

Theorem concretize_delegate_clean_snapshots:
  concretize_supplement D tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = DELEGATECALL ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >> irule concretize_supplement_clean_accounts >>
  gvs[taint_ok_def] >> metis_tac[]
QED

Theorem concretize_delegate_input_clean:
  relocation_reader_context s t /\ relocation_env s t /\
  concretize_supplement D tn s t /\ taint_ok fn tn inst s /\
  inst.inst_opcode = DELEGATECALL ==>
  make_venom_delegatecall_state s target gas calldata code is_static =
  make_venom_delegatecall_state t target gas calldata code is_static
Proof
  strip_tac >> drule_all concretize_delegate_clean_snapshots >> strip_tac >>
  irule concretize_delegate_input >> gvs[relocation_env_def]
QED
