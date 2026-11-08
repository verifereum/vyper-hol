Theory deadStoreElimExternalObservations
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimDefs
  deadStoreElimFrameReadSteps venomExecSemantics venomState vfmState
  deadStoreElimFrame
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

(* Observations insensitive to the account's storage map survive pending
 * storage differences, even at the currently executing contract. *)
Theorem dse_local_agrees_account_observation:
  (!a st. observe (a with storage := st) = observe a) /\
  dse_local_agrees sp P s t ==>
  observe (lookup_account addr s.vs_accounts) =
  observe (lookup_account addr t.vs_accounts)
Proof
  strip_tac >>
  Cases_on `sp = AddrSp_Storage`
  >- (fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
      Cases_on `addr = s.vs_call_ctx.cc_address`
      >- (gvs[lookup_account_def] >>
          qpat_x_assum `dse_accounts_normalize _ _ _ = _`
            (fn th => mp_tac (Q.AP_THM th `t.vs_call_ctx.cc_address`)) >>
          simp[dse_accounts_normalize_def, combinTheory.APPLY_UPDATE_THM] >>
          metis_tac[]) >>
      fs[lookup_account_def] >> metis_tac[dse_accounts_normalize_other]) >>
  fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED

Theorem dse_local_agrees_account_balance:
  dse_local_agrees sp P s t ==>
  (lookup_account addr s.vs_accounts).balance =
  (lookup_account addr t.vs_accounts).balance
Proof
  strip_tac >> irule dse_local_agrees_account_observation >>
  simp[] >> goal_assum drule
QED

Theorem dse_local_agrees_account_empty:
  dse_local_agrees sp P s t ==>
  account_empty (lookup_account addr s.vs_accounts) =
  account_empty (lookup_account addr t.vs_accounts)
Proof
  strip_tac >> irule dse_local_agrees_account_observation >>
  simp[vfmStateTheory.account_empty_def] >> goal_assum drule
QED
