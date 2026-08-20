(*
 * Machine-typing preservation for checked external calls.
 *
 * TOP-LEVEL:
 * - call_external_failure_rolls_back
 * - checked_call_external_failure_preserves_machine_well_typed
 * - checked_call_external_success_preserves_machine_well_typed
 * - checked_call_external_preserves_machine_well_typed
 *)

Theory vyperTypeExternalCallMachine
Ancestors
  list rich_list finite_map option pair
  vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeInvariants vyperTypeInitialState
  vyperTypeEntryReadiness vyperTypeContractSoundness
  vyperStatePreservation vyperScopePreservation
Libs
  wordsLib

val _ = Parse.hide "body";

(* ===== Lock/unlock preservation ===== *)

Theorem release_nonreentrant_lock_machine_components:
  release_nonreentrant_lock target slot st = (res,st') ==>
  st'.scopes = st.scopes /\
  st'.immutables = st.immutables /\
  st'.accounts = st.accounts
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem release_action_preserves_machine_components:
  (if nr /\ ~is_view then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes /\
  st'.immutables = st.immutables /\
  st'.accounts = st.accounts
Proof
  rw[] >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  metis_tac[release_nonreentrant_lock_machine_components]
QED

(* ===== Failure rollback ===== *)

(* The direct proof is retained from the initial composition attempt.  The
 * execution-result case split will be discharged after the prefix/body helper
 * below is in place.
Theorem call_external_failure_rolls_back:
  call_external am tx = (INR exc,am') ==> am' = am
Proof
  rw[call_external_def] >> gvs[AllCaseEqs()] >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def, initial_evaluation_context_def] >>
  strip_tac >> gvs[AllCaseEqs(), initial_evaluation_context_def]
QED
*)

(* ===== Successful selected entries ===== *)

(* Migrated from vyperTypeContractSoundnessScript.sml.  It is intentionally
 * preserved here while the lock/send/body result helper is factored.
Theorem call_external_function_selected_explicit_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  evaluate_defaults cx am
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) = SOME dflt_vs /\
  bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) = SOME scope /\
  call_external_function am cx nr mut ts mods args dflts vals body ret =
    (INL v,am') ==>
  machine_well_typed am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def]
QED
*)

val _ = export_theory();
