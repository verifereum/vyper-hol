(*
 * The finite storage invariant across the parts of an external call that
 * surround its body.
 *
 * storage_well_formed_on cx st L reads only the contract's two storage
 * backends (get_storage cx st T and F).  So everything call_external does
 * around the body keeps it for any root list L: the call-value transfer
 * moves only balances, the machine round trip through
 * abstract_machine_from_state and initial_state keeps both backends, and
 * committing pending deletions only zeroes deleted accounts' storage,
 * which is in range at every root.
 *
 * TOP-LEVEL:
 *   storage_well_formed_on_storage_frame
 *   transfer_value_preserves_storage_well_formed_on
 *   send_call_value_preserves_storage_well_formed_on
 *   storage_well_formed_on_initial_abstract_machine
 *   finalize_pending_deletions_preserves_storage_well_formed_on
 *)

Theory vyperCallStorageFootprint
Ancestors
  vfmState vfmExecution
  vyperState vyperInterpreter vyperStorage vyperStorageBackend vyperLookupStorage
  vyperStorageFootprint vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation

Theorem storage_well_formed_on_storage_frame:
  (!b. get_storage cx st' b = get_storage cx st b) ==>
  (storage_well_formed_on cx st' regions <=>
   storage_well_formed_on cx st regions)
Proof
  simp[storage_well_formed_on_def]
QED

Theorem transfer_value_preserves_storage_well_formed_on:
  storage_well_formed_on cx st regions /\
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >> drule transfer_value_storage_frame >>
  disch_then (qspec_then `cx` assume_tac) >>
  drule storage_well_formed_on_storage_frame >> simp[]
QED

Theorem send_call_value_preserves_storage_well_formed_on:
  storage_well_formed_on cx st regions /\
  send_call_value mut cx st = (res,st') ==>
  storage_well_formed_on cx st' regions
Proof
  simp[send_call_value_def] >> IF_CASES_TAC >>
  simp[return_def, bind_def, ignore_bind_def, check_def, assert_def,
       raise_def] >>
  Cases_on `mut = Payable` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[transfer_value_preserves_storage_well_formed_on]
QED

Theorem storage_well_formed_on_initial_abstract_machine:
  storage_well_formed_on cx
    (initial_state (abstract_machine_from_state srcs exps layouts st) scs)
    regions <=>
  storage_well_formed_on cx st regions
Proof
  irule storage_well_formed_on_storage_frame >> Cases >>
  simp[get_storage_def, initial_state_def, abstract_machine_from_state_def]
QED

(* A deleted account's storage reads zero at every slot. *)
Theorem process_deletions_storage:
  !ds accounts a.
    (process_deletions ds accounts a).storage = (accounts a).storage \/
    (process_deletions ds accounts a).storage = empty_storage
Proof
  Induct >> simp[process_deletions_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`update_account h empty_account_state accounts`, `a`] strip_assume_tac) >>
  gvs[update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `h = a` >> gvs[empty_account_state_def]
QED

Theorem finalize_pending_deletions_preserves_storage_well_formed_on:
  storage_well_formed_on cx (initial_state am scs) regions ==>
  storage_well_formed_on cx
    (initial_state (finalize_pending_deletions am) scs) regions
Proof
  rw[storage_well_formed_on_def] >> first_x_assum drule >>
  Cases_on `b` >>
  gvs[get_storage_def, initial_state_def, finalize_pending_deletions_def] >>
  qspecl_then [`am.pending_deletions`, `am.accounts`, `cx.txn.target`]
    strip_assume_tac process_deletions_storage >>
  simp[] >> strip_tac >>
  irule (cj 1 zero_read_slots_in_range_mutual) >>
  simp[read_slot_def, lookup_storage_def, empty_storage_def]
QED
