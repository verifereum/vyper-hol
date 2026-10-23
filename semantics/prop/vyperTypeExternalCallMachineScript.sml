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
  vyperTypeContractFunction vyperTypeContractGetter
  vyperTypeContractSoundness vyperTypeExternalDefaults vyperExprNoControl
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
   else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (INL (),lock_st) /\
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
     qexistsl [`cx`, `mut`, `nr`, `orc`, `rqs`] >> simp[bind_def, ignore_bind_def]) >>
  `lock_st.accounts =
     (initial_state am [scope] with <|outcomes := orc; requests := rqs|>).accounts` by
    metis_tac[call_lock_action_preserves_accounts_c53] >>
  `accounts_well_typed lock_st.accounts` by
    gvs[initial_state_accounts_well_typed_simple] >>
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
   else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (INL (),lock_st) /\
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
     qexistsl [`cx`, `lock_st`, `mut`, `nr`, `orc`, `rqs`] >> simp[]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (`check_function_body am.layouts tx.target mods art src mut nr
       args dflts ret body` by
       (irule check_contract_runtime_function_body_MEM >> simp[] >>
        qexistsl [`tx.function_name`, `raw`, `External`] >> simp[]) >>
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
   else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (INL (),lock_st) /\
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
     qexistsl [`cx`, `lock_st`, `mut`, `nr`, `orc`, `rqs`] >> simp[]) >>
  irule checked_public_getter_body_preserves_machine_components >>
  simp[] >> metis_tac[]
QED

Theorem checked_getter_send_eval_success_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (View,F,args,[],ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (do send_call_value View cx; eval_stmts cx body
   od (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st')) /\
  (res = INL () \/ ?v. res = INR (ReturnException v)) ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  qpat_x_assum `do _; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `send_call_value View
    (initial_evaluation_context am.sources am.layouts tx src)
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` >>
  Cases_on `q` >> gvs[]
  >- (rpt strip_tac >>
      mp_tac (GEN_ALL (Q.INST
        [`mut` |-> `View`, `nr` |-> `F`, `dflts` |-> `[]`,
         `cx` |-> `initial_evaluation_context am.sources am.layouts tx src`,
         `lock_st` |-> `initial_state am [scope] with <|outcomes := orc; requests := rqs|>`]
        (SPEC_ALL checked_getter_body_from_states_preserves_components))) >>
      simp[return_def] >> disch_then drule_all >> simp[])
  >- (rpt strip_tac >>
      mp_tac (GEN_ALL (Q.INST
        [`mut` |-> `View`, `nr` |-> `F`, `dflts` |-> `[]`,
         `cx` |-> `initial_evaluation_context am.sources am.layouts tx src`,
         `lock_st` |-> `initial_state am [scope] with <|outcomes := orc; requests := rqs|>`]
        (SPEC_ALL checked_getter_body_from_states_preserves_components))) >>
      simp[return_def] >> disch_then drule_all >> simp[])
  >- (rpt strip_tac >>
      FIRST
        [drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
         simp[no_control_exc_def],
         `return () (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) =
          (INL (),initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` by simp[return_def] >>
         funpow 6 drule_then drule
           checked_getter_body_from_states_preserves_components >>
         simp[] >> disch_then (drule_then drule) >> gvs[]])
  >- (rpt strip_tac >>
      FIRST
        [drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
         simp[no_control_exc_def],
         `return () (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) =
          (INL (),initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` by simp[return_def] >>
         funpow 6 drule_then drule
           checked_getter_body_from_states_preserves_components >>
         simp[] >> disch_then (drule_then drule) >> gvs[]])
  >- (rpt strip_tac >>
      FIRST
        [drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
         simp[no_control_exc_def],
         `return () (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) =
          (INL (),initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` by simp[return_def] >>
         funpow 6 drule_then drule
           checked_getter_body_from_states_preserves_components >>
         simp[] >> disch_then (drule_then drule) >> gvs[]])
  >- (strip_tac >>
      drule_at(Pat`send_call_value`) send_call_value_no_control_c53 >>
      simp[no_control_exc_def])
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
   od (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st')) /\
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
             else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs|>)` >>
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

Theorem call_external_function_nondeploy_failure_rolls_back:
  ~cx.in_deploy /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INR exc,am',rqs) ==>
  am' = am
Proof
  strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def] >>
  IF_CASES_TAC >- simp[] >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  Cases_on `q` >> simp_tac (srw_ss()) []
  >- (rpt (BasicProvers.TOP_CASE_TAC >> simp_tac (srw_ss()) []) >> metis_tac[]) >>
  Cases_on `y` >> simp_tac (srw_ss()) [] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp_tac (srw_ss()) []) >> metis_tac[]
QED

Theorem call_external_function_initial_failure_rolls_back:
  call_external_function orc am
    (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (INR exc,am',rqs) ==>
  am' = am
Proof
  strip_tac >>
  `~(initial_evaluation_context am.sources am.layouts tx src).in_deploy` by
    simp[initial_evaluation_context_def] >>
  drule_all call_external_function_nondeploy_failure_rolls_back >> simp[]
QED

Theorem call_external_failure_rolls_back:
  call_external orc am tx = (INR exc,am',rqs) ==> am' = am
Proof
  rw[call_external_def] >> gvs[AllCaseEqs()] >>
  metis_tac[call_external_function_initial_failure_rolls_back]
QED

Theorem checked_call_external_failure_preserves_machine_well_typed:
  machine_well_typed am /\ call_external orc am tx = (INR exc,am',rqs) ==>
  machine_well_typed am'
Proof
  metis_tac[call_external_failure_rolls_back]
QED

(* ===== Successful selected entries ===== *)

Theorem call_external_function_selected_explicit_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_well_typed am'
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed cx` by
    gvs[call_tx_well_typed_def, context_well_typed_def,
        initial_evaluation_context_def] >>
  `state_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>) /\
   accounts_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>).accounts` by
    gvs[initial_state_def, state_well_typed_def, machine_well_typed_def, scope_well_typed_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>).immutables` by
    (simp_tac (srw_ss()) [initial_state_def] >>
     metis_tac[checked_contract_runtime_ready_def,
               immutables_ready_initial_evaluation_context_source]) >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_def, LET_THM] >>
  `cx.in_deploy = F` by simp[initial_evaluation_context_def] >>
  qpat_assum `cx.in_deploy = F` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  IF_CASES_TAC >- gvs[] >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []|>)` >>
  strip_tac >> drule external_call_result_success_cases >> strip_tac >>
  `state_well_typed st_body /\ accounts_well_typed st_body.accounts` by
    (qpat_x_assum `entry _ = _` mp_tac >>
     simp_tac bool_ss [Abbr `entry`] >> strip_tac >>
     drule_all checked_external_entry_sound >> simp[]) >>
  gvs[] >> irule release_action_success_machine_well_typed >>
  qexistsl [`initial_evaluation_context am.sources am.layouts tx src`,
            `mut = View \/ mut = Pure`, `nr`, `st_body`] >> simp[]
QED

Theorem checked_getter_initial_body_components:
  eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
    (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) = (res,st') ==>
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,(dflts : expr list),ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `state_well_typed (initial_state am [scope] with <|outcomes := orc; requests := rqs|>) /\
   accounts_well_typed (initial_state am [scope] with <|outcomes := orc; requests := rqs|>).accounts` by
    gvs[initial_state_def, state_well_typed_def, machine_well_typed_def] >>
  gvs[initial_state_def] >>
  drule_all (Q.INST
    [`cx` |-> `initial_evaluation_context am.sources am.layouts tx src`,
     `st` |-> `initial_state am [scope] with <|outcomes := orc; requests := rqs|>`]
    (SPEC_ALL checked_public_getter_body_preserves_machine_components)
    |> SIMP_RULE (srw_ss()) [initial_state_def] |> GEN_ALL) >>
  simp[]
QED

Theorem call_external_function_selected_getter_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_well_typed am'
Proof
  rpt strip_tac >>
  `nr = F /\ mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
     >- (rename1 `is_public_getter_decl _
           (VariableDecl vis storage id ty init)` >>
         Cases_on `vis` >> gvs[is_public_getter_decl_def] >>
         Cases_on `storage` >> gvs[] >>
         Cases_on `is_ArrayT ty` >> gvs[] >>
         FIRST
           [drule_all array_public_getter_tuple_shape >> metis_tac[],
            gvs[external_getter_tuple_def]]) >>
     rename1 `is_public_getter_decl _
       (HashMapDecl vis transient id kt vt init)` >>
     Cases_on `vis` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_def, LET_THM] >>
  simp[initial_evaluation_context_def] >>
  Cases_on `tx.value = 0` >>
  simp[send_call_value_def, bind_def, ignore_bind_def, return_def,
       check_def, assert_def, raise_def, set_scopes_def, initial_state_def] >>
  strip_tac >>
  qpat_x_assum `(\(res,am_out,rqs). _) _ = _` mp_tac >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[AllCaseEqs()] >> strip_tac >>
  rename1 `eval_stmts _ _ _ = (res, st_body)` >>
  `state_well_typed st_body /\ accounts_well_typed st_body.accounts` by
    (drule (SRULE [initial_evaluation_context_def, initial_state_def]
       checked_getter_initial_body_components) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  gvs[return_def, machine_well_typed_def, abstract_machine_from_state_def,
      state_well_typed_def]
QED

(* Deleting only accounts queued by SELFDESTRUCT preserves account typing. *)
Theorem accounts_well_typed_process_deletions:
  !pending accounts.
    accounts_well_typed accounts ==>
    accounts_well_typed (vfmExecution$process_deletions pending accounts)
Proof
  Induct >> simp[vfmExecutionTheory.process_deletions_def] >>
  metis_tac[vyperTypeExtCallSoundnessTheory.accounts_well_typed_update_account,
            vyperTypeExtCallSoundnessTheory.account_well_typed_empty_account_state]
QED

Theorem finalize_pending_deletions_machine_well_typed:
  machine_well_typed am ==>
  machine_well_typed (finalize_pending_deletions am)
Proof
  simp[machine_well_typed_def, finalize_pending_deletions_def,
       accounts_well_typed_process_deletions]
QED

Theorem checked_call_external_success_preserves_machine_well_typed:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  checked_external_call_inputs_ready am tx /\
  call_external orc am tx = (INL v,am',rqs) ==>
  machine_well_typed am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external orc am tx = _` mp_tac >>
  simp[Once call_external_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[checked_contract_runtime_ready_def, get_self_code_def] >>
  `checked_call_inputs_ready
     (type_env_all_modules all_mods)
     (initial_evaluation_context am.sources am.layouts tx
       (find_function_module am tx.target tx.function_name))
     am args dflts tx.args` by (
    irule checked_external_call_inputs_ready_selected >>
    simp[] >> metis_tac[]) >>
  `(?raw.
      MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts) \/
   (?decl.
      MEM decl ts /\
      is_public_getter_decl tx.function_name decl /\
      external_getter_tuple (find_function_module am tx.target tx.function_name) decl =
        SOME (mut,nr,args,dflts,ret,body'))` by
    (irule lookup_exported_function_checked_cases_current >> simp[] >> metis_tac[]) >>
  irule finalize_pending_deletions_machine_well_typed >>
  `ALOOKUP all_mods (find_function_module am tx.target tx.function_name) = SOME ts` by
    gvs[get_module_code_def, initial_evaluation_context_def] >>
  `checked_contract_runtime_ready art all_mods am tx` by
    gvs[checked_contract_runtime_ready_def] >>
  `LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts` by
    gvs[checked_call_inputs_ready_def, checked_defaults_ready_def] >>
  TRY (qpat_assum `MEM (FunctionDecl External _ _ _ _ _ _ _ _) _` (fn _ => all_tac) >>
     drule_at (Pat `call_external_function`)
       call_external_function_selected_explicit_success_machine_well_typed >>
     simp[] >> disch_then (fn th => metis_tac[th]) >> NO_TAC) >>
  (`nr = F /\ mut = View /\ dflts = []` by
       (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
        >- (rename1 `is_public_getter_decl _ (VariableDecl vis storage id ty init)` >>
            Cases_on `vis` >> gvs[is_public_getter_decl_def] >>
            Cases_on `storage` >> gvs[] >> Cases_on `is_ArrayT ty` >> gvs[] >>
            FIRST [drule_all array_public_getter_tuple_shape >> metis_tac[],
                   gvs[external_getter_tuple_def]]) >>
        rename1 `is_public_getter_decl _ (HashMapDecl vis transient id kt vt init)` >>
        Cases_on `vis` >> gvs[is_public_getter_decl_def] >>
        drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
      gvs[] >>
      `?scope. bind_arguments (type_env_all_modules all_mods) args tx.args = SOME scope` by
        (drule call_external_function_success_phases >>
         simp[eval_external_defaults_nil] >> metis_tac[]) >>
      drule_at (Pat `call_external_function`)
        call_external_function_selected_getter_success_machine_well_typed >>
      simp[] >>
      disch_then (fn th => metis_tac[th]))
QED

Theorem checked_call_external_preserves_machine_well_typed:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  checked_external_call_inputs_ready am tx /\
  call_external orc am tx = (res,am',rqs) ==>
  machine_well_typed am'
Proof
  Cases_on `res` >> strip_tac
  >- metis_tac[checked_call_external_success_preserves_machine_well_typed] >>
  metis_tac[checked_call_external_failure_preserves_machine_well_typed]
QED

(* Machine preservation must not inherit admitted prerequisites. *)
val () = List.app (fn (_, th) =>
  if List.null (List.filter (fn s => s <> "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "external call machine preservation has oracle dependencies")
  (DB.thms "vyperTypeExternalCallMachine");
