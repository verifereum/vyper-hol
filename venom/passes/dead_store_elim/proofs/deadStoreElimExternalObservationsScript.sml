Theory deadStoreElimExternalObservations
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimDefs
  deadStoreElimFrameReadSteps venomExecSemantics venomState
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_local_agrees_prev_hashes:
  dse_local_agrees sp P s t ==> s.vs_prev_hashes = t.vs_prev_hashes
Proof
  simp[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED

Theorem dse_local_agrees_memory_accounts:
  dse_local_agrees AddrSp_Memory P s t ==> s.vs_accounts = t.vs_accounts
Proof
  simp[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED

Theorem dse_local_agrees_memory_transient:
  dse_local_agrees AddrSp_Memory P s t ==> s.vs_transient = t.vs_transient
Proof
  simp[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED

Theorem dse_local_agrees_tx_params:
  dse_local_agrees sp P s t ==> venom_to_tx_params s = venom_to_tx_params t
Proof
  strip_tac >> drule dse_local_agrees_frame >> strip_tac >>
  drule dse_local_agrees_prev_hashes >> strip_tac >>
  simp[venom_to_tx_params_def]
QED

Theorem dse_local_agrees_call_state:
  dse_local_agrees AddrSp_Memory P s t ==>
  make_venom_call_state s target gas value bytes code static =
  make_venom_call_state t target gas value bytes code static
Proof
  strip_tac >> drule dse_local_agrees_frame >> strip_tac >>
  drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  drule dse_local_agrees_tx_params >> strip_tac >>
  simp[make_venom_call_state_def]
QED

Theorem dse_local_agrees_delegatecall_state:
  dse_local_agrees AddrSp_Memory P s t ==>
  make_venom_delegatecall_state s target gas bytes code static =
  make_venom_delegatecall_state t target gas bytes code static
Proof
  strip_tac >> drule dse_local_agrees_frame >> strip_tac >>
  drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  drule dse_local_agrees_tx_params >> strip_tac >>
  simp[make_venom_delegatecall_state_def]
QED

Theorem dse_local_agrees_create_state:
  dse_local_agrees AddrSp_Memory P s t ==>
  make_venom_create_state s addr gas value bytes =
  make_venom_create_state t addr gas value bytes
Proof
  strip_tac >> drule dse_local_agrees_frame >> strip_tac >>
  drule dse_local_agrees_memory_accounts >> strip_tac >>
  drule dse_local_agrees_memory_transient >> strip_tac >>
  drule dse_local_agrees_tx_params >> strip_tac >>
  simp[make_venom_create_state_def]
QED
