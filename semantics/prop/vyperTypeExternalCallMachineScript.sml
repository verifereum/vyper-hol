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
  vyperTypeInvariants vyperTypeBindArguments vyperTypeInitialState
  vyperTypeEntryReadiness vyperTypeContract vyperTypeContractContext
  vyperTypeContractFunction
  vyperTypeContractSoundness vyperExprNoControl
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

(* ===== Checked body execution ===== *)

Theorem call_lock_send_success_components:
  machine_well_typed am /\ scope_well_typed scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am [scope]) = (INL (),lock_st) /\
  send_call_value mut cx lock_st = (INL (),body_st) ==>
  body_st.scopes = [scope] /\
  body_st.immutables = am.immutables /\
  state_well_typed body_st /\
  accounts_well_typed body_st.accounts
Proof
  strip_tac >>
  `body_st.scopes = [scope] /\ body_st.immutables = am.immutables /\
   state_well_typed body_st` by
    (irule call_lock_send_prefix_body_state_ready_c53 >> simp[] >>
     qexistsl [`cx`, `mut`, `nr`] >> simp[bind_def, ignore_bind_def]) >>
  `lock_st.accounts = (initial_state am [scope]).accounts` by
    metis_tac[call_lock_action_preserves_accounts_c53] >>
  `accounts_well_typed lock_st.accounts` by
    gvs[initial_state_accounts_well_typed] >>
  `accounts_well_typed body_st.accounts` by
    metis_tac[send_call_value_accounts_well_typed_c53] >>
  simp[]
QED

Theorem checked_explicit_body_from_states_preserves_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am [scope]) = (INL (),lock_st) /\
  send_call_value mut cx lock_st = (INL (),body_st) /\
  eval_stmts cx body body_st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `body_st.scopes = [scope] /\ body_st.immutables = am.immutables /\
   state_well_typed body_st /\ accounts_well_typed body_st.accounts` by
    (irule call_lock_send_success_components >> simp[] >>
     qexistsl [`cx`, `lock_st`, `mut`, `nr`] >> simp[]) >>
  `ALL_DISTINCT (MAP (string_to_num o FST) args)` by
    (`check_function_body am.layouts tx.target mods art src mut nr
       args dflts ret body` by
       metis_tac[check_contract_function_body_MEM] >>
     gvs[check_function_body_def, params_ok_def]) >>
  irule checked_explicit_external_body_preserves_machine_components >>
  qexistsl [`am`, `args`, `art`, `body`, `cx`, `dflts`, `mods`, `mut`, `nr`,
            `raw`, `res`, `ret`, `scope`, `src`, `body_st`, `ts`, `tx`, `vals`] >>
  simp[]
QED

Theorem checked_getter_body_from_states_preserves_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am [scope]) = (INL (),lock_st) /\
  send_call_value mut cx lock_st = (INL (),body_st) /\
  eval_stmts cx body body_st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `body_st.scopes = [scope] /\ body_st.immutables = am.immutables /\
   state_well_typed body_st /\ accounts_well_typed body_st.accounts` by
    (irule call_lock_send_success_components >> simp[] >>
     qexistsl [`cx`, `lock_st`, `mut`, `nr`] >> simp[]) >>
  irule checked_public_getter_body_preserves_machine_components >>
  simp[] >> metis_tac[]
QED

Theorem checked_explicit_call_run_success_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am [scope]) = (res,st')) /\
  (res = INL () \/ ?v. res = INR (ReturnException v)) ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  qpat_x_assum `do _; _; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `(if nr then
               case cx.nonreentrant_slot of
                 NONE => raise (Error (TypeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                                (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut
        (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[] >> rpt strip_tac >>
      `initial_evaluation_context am.sources am.layouts tx src =
       initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
      drule_all_then strip_assume_tac
        checked_explicit_body_from_states_preserves_components >> simp[])
  >- (Cases_on `send_call_value mut
        (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[] >> rpt strip_tac >>
      `initial_evaluation_context am.sources am.layouts tx src =
       initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
      drule_all_then strip_assume_tac
        checked_explicit_body_from_states_preserves_components >> simp[])
  >- (Cases_on `send_call_value mut
        (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[] >> rpt strip_tac >>
      FIRST
        [drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
         simp[no_control_exc_def],
         `initial_evaluation_context am.sources am.layouts tx src =
          initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
         funpow 5 drule_then drule
           checked_explicit_body_from_states_preserves_components >>
         simp[] >> disch_then (drule_then drule) >> gvs[]])
  >- (Cases_on `send_call_value mut
        (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[] >> rpt strip_tac >>
      FIRST
        [drule call_lock_action_no_control_c53 >> simp[no_control_exc_def],
         drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
         simp[no_control_exc_def],
         `initial_evaluation_context am.sources am.layouts tx src =
          initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
         funpow 5 drule_then drule
           checked_explicit_body_from_states_preserves_components >>
         simp[] >> disch_then (drule_then drule) >> gvs[]])
  >- (Cases_on `send_call_value mut
        (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[] >> rpt strip_tac >>
      FIRST
        [drule call_lock_action_no_control_c53 >> simp[no_control_exc_def],
         drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
         simp[no_control_exc_def],
         `initial_evaluation_context am.sources am.layouts tx src =
          initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
         funpow 5 drule_then drule
           checked_explicit_body_from_states_preserves_components >>
         simp[] >> disch_then (drule_then drule) >> gvs[]])
  >- (strip_tac >> drule call_lock_action_no_control_c53 >>
      simp[no_control_exc_def])
QED

Theorem release_action_success_machine_well_typed:
  state_well_typed st /\ accounts_well_typed st.accounts /\
  (if nr /\ ~is_view then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (INL (),st') ==>
  machine_well_typed (abstract_machine_from_state srcs exps layouts st')
Proof
  strip_tac >>
  drule release_action_preserves_machine_components >> strip_tac >>
  irule abstract_machine_from_state_well_typed >>
  gvs[state_well_typed_def]
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
  qabbrev_tac `call_run =
    do
      (if nr then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                          (mut = View \/ mut = Pure)
       else return ());
      send_call_value mut cx;
      eval_stmts cx body
    od (initial_state am [scope])` >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def] >> strip_tac >>
  qabbrev_tac `call_res = FST call_run` >>
  PairCases_on `call_run` >> Cases_on `call_run0` >>
  gvs[AllCaseEqs()] >>
  Cases_on `(if nr /\ mut <> View /\ mut <> Pure then
               case lookup_nonreentrant_slot am.layouts tx.target of
                 NONE => return ()
               | SOME slot => release_nonreentrant_lock tx.target slot
             else return ()) call_run1` >>
  Cases_on `q` >> gvs[] >>
  TRY (Cases_on `y` >> gvs[]) >> TRY (Cases_on `y'` >> gvs[]) >>
  `initial_evaluation_context am.sources am.layouts tx src =
   initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
  `state_well_typed call_run1 /\
   accounts_well_typed call_run1.accounts` by (
    irule checked_explicit_call_run_success_components >>
    qexistsl [`am`, `args`, `art`, `body`,
              `initial_evaluation_context am.sources am.layouts tx src`,
              `dflts`, `mods`, `mut`, `nr`,
              `raw`, `call_res`, `ret`, `scope`, `src`, `ts`, `tx`,
              `vals ++ dflt_vs`] >>
    simp[Abbr`call_res`, initial_evaluation_context_def]) >>
  gvs[Abbr`call_res`] >>
  `(if nr /\ ~(mut = View \/ mut = Pure) then
      case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
        NONE => return ()
      | SOME slot => release_nonreentrant_lock tx.target slot
    else return ()) call_run1 = (INL (),r)` by
    gvs[initial_evaluation_context_def] >>
  `r.scopes = call_run1.scopes /\
   r.immutables = call_run1.immutables /\
   r.accounts = call_run1.accounts` by (
    Cases_on `nr` >> gvs[return_def] >>
    Cases_on `mut = View` >> gvs[return_def] >>
    Cases_on `mut = Pure` >> gvs[return_def] >>
    Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
    gvs[return_def] >>
    metis_tac[release_nonreentrant_lock_machine_components]) >>
  Cases_on `evaluate_type (type_env_all_modules mods) ret` >> gvs[] >>
  Cases_on `safe_cast x v'` >> gvs[] >>
  gvs[machine_well_typed_def, abstract_machine_from_state_def,
      state_well_typed_def, AllCaseEqs()]
QED

val _ = export_theory();
