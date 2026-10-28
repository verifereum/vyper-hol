(*
 * Properties of accounts_rel (#665): the state_rel component that relates
 * every address's accounts and transient storage, with no source pending
 * deletions.
 *
 * TOP-LEVEL:
 *   state_rel_accounts      — state_rel gives the accounts and transient
 *                             storage the success case of the external
 *                             result relation compares
 *   accounts_rel_set_storage, accounts_rel_set_transient — a write of the
 *                             running contract's storage or transient
 *                             storage on both sides keeps accounts_rel
 *   accounts_rel_sstore, accounts_rel_tstore — their case for one SSTORE
 *                             or TSTORE
 *   accounts_rel_take_call_outcome, accounts_rel_adopt_call_outcome — the
 *                             call oracle keeps accounts_rel: taking an
 *                             outcome changes neither side's accounts, and
 *                             both sides adopt it with adopt_outcome
 *   accounts_rel_call_request — the oracle requests of the two sides carry
 *                             the same accounts and transient storage
 *
 * Helper:
 *   accounts_rel_storage_transient — storage_rel and transient_rel are
 *                             accounts_rel's case for the running contract
 *   accounts_rel_frame, accounts_rel_updates — accounts_rel reads only
 *                             the accounts, transient storage and pending
 *                             deletions
 *)

Theory accountsRelProps
Ancestors
  compileEnv vyperState vyperCallOutcome extCallOracle
  venomState venomCallOracleDefs vfmExecution vfmState

(* ===== The success-case effects ===== *)

Theorem state_rel_accounts:
  !func cenv cx es s.
    state_rel func cenv cx es s ==>
    s.vs_accounts = process_deletions es.pending_deletions es.accounts /\
    s.vs_transient = es.tStorage
Proof
  rw[state_rel_def, accounts_rel_def, process_deletions_def]
QED

Theorem accounts_rel_storage_transient:
  !es s.
    accounts_rel es s ==>
    storage_rel s.vs_call_ctx.cc_address es s /\
    transient_rel s.vs_call_ctx.cc_address es s
Proof
  rw[accounts_rel_def, storage_rel_def, transient_rel_def,
     contract_storage_def, contract_transient_def]
QED

(* ===== Frames ===== *)

(* accounts_rel reads only the accounts, transient storage and pending
   deletions of the source and the accounts and transient storage of
   Venom. *)
Theorem accounts_rel_frame:
  !es es' s s'.
    es'.accounts = es.accounts /\ es'.tStorage = es.tStorage /\
    es'.pending_deletions = es.pending_deletions /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient ==>
    (accounts_rel es' s' <=> accounts_rel es s)
Proof
  simp[accounts_rel_def]
QED

Theorem accounts_rel_updates[simp]:
  (!es s x w. accounts_rel es (update_var x w s) <=> accounts_rel es s) /\
  (!es s V. accounts_rel es (s with vs_vars := V) <=> accounts_rel es s) /\
  (!es s lbl. accounts_rel es (jump_to lbl s) <=> accounts_rel es s) /\
  (!es s n. accounts_rel es (s with vs_inst_idx := n) <=>
            accounts_rel es s) /\
  (!es s sc. accounts_rel (es with scopes := sc) s <=> accounts_rel es s)
Proof
  simp[accounts_rel_def, update_var_def, jump_to_def]
QED

(* ===== Writes of the running contract's storage ===== *)

(* The source sets the storage of cx.txn.target to stor, and Venom that of
   the running contract, the same address. *)
Theorem accounts_rel_set_storage:
  !cx stor es es' s s'.
    accounts_rel es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    set_storage_backend cx F stor es = (INL (), es') /\
    s'.vs_accounts =
      (cx.txn.target =+
         (lookup_account cx.txn.target s.vs_accounts with storage := stor))
        s.vs_accounts /\
    s'.vs_transient = s.vs_transient ==>
    accounts_rel es' s'
Proof
  gvs[set_storage_backend_def, vyperStateTheory.bind_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
      vyperStateTheory.return_def, accounts_rel_def, update_account_def]
QED

Theorem accounts_rel_set_transient:
  !cx stor es es' s s'.
    accounts_rel es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    set_storage_backend cx T stor es = (INL (), es') /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = (cx.txn.target =+ stor) s.vs_transient ==>
    accounts_rel es' s'
Proof
  rw[set_storage_backend_def, vyperStateTheory.update_transient_def,
     vyperStateTheory.return_def] >>
  gvs[accounts_rel_def, update_transient_storage_def]
QED

Theorem accounts_rel_sstore:
  !cx k v es es' s.
    accounts_rel es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    set_storage_backend cx F (update_storage k v (contract_storage s)) es =
      (INL (), es') ==>
    accounts_rel es' (sstore k v s)
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `update_storage k v (contract_storage s)`, `es`, `es'`, `s`,
               `sstore k v s`] mp_tac accounts_rel_set_storage >>
  simp[sstore_def, contract_storage_def]
QED

Theorem accounts_rel_tstore:
  !cx k v es es' s.
    accounts_rel es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
    set_storage_backend cx T (update_storage k v (contract_transient s)) es =
      (INL (), es') ==>
    accounts_rel es' (tstore k v s)
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `update_storage k v (contract_transient s)`, `es`, `es'`, `s`,
               `tstore k v s`] mp_tac accounts_rel_set_transient >>
  simp[tstore_def, contract_transient_def]
QED

(* ===== The call oracle ===== *)

Theorem accounts_rel_take_call_outcome:
  !target calldata value_opt es es' res s.
    accounts_rel es s /\
    take_call_outcome target calldata value_opt es = (res, es') ==>
    accounts_rel es' s
Proof
  rpt strip_tac >> drule take_call_outcome_frame >> strip_tac >>
  pop_assum SUBST1_TAC >> fs[accounts_rel_def]
QED

(* Both sides adopt accounts, transient storage, logs and pending deletions
   with adopt_outcome.  Preserving accounts_rel's supported-subset empty
   list requires an adopted outcome to add no pending deletions. *)
Theorem accounts_rel_adopt_call_outcome:
  !rq outcome es es' s s' logs.
    accounts_rel es s /\ adopt_call_outcome rq outcome es = (INL (), es') /\
    (outcome.co_success /\ ~rq.cr_static ==> outcome.co_toDelete = []) /\
    s'.vs_accounts =
      FST (adopt_outcome rq outcome
             (s.vs_accounts, s.vs_transient, logs, s.vs_pending_deletions)) /\
    s'.vs_transient =
      FST (SND (adopt_outcome rq outcome
                  (s.vs_accounts, s.vs_transient, logs,
                   s.vs_pending_deletions))) ==>
    accounts_rel es' s'
Proof
  rw[adopt_call_outcome_equation] >>
  gvs[accounts_rel_def, adopt_outcome_def] >>
  rw[] >> gvs[]
QED

Theorem accounts_rel_call_request:
  !es s target calldata value_opt.
    accounts_rel es s ==>
    (call_outcome_request target calldata value_opt es).cr_accounts =
      s.vs_accounts /\
    (call_outcome_request target calldata value_opt es).cr_tStorage =
      s.vs_transient
Proof
  rw[accounts_rel_def, call_outcome_request_def]
QED
