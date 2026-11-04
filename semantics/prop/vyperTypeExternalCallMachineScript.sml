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
  vyperSourceSupplyDefs vyperSourceSupplyFields vyperEvalSupply
Libs
  wordsLib vyperSourceSupplyLib

val _ = Parse.hide "body";

val machine_gvs = gvs;
val machine_drule_all = drule_all;
fun gvs ths = vyperSourceSupplyLib.forward >> machine_gvs ths >>
  vyperSourceSupplyLib.forward;
fun drule_all th = vyperSourceSupplyLib.forward >> machine_drule_all th;

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

Theorem call_lock_action_error:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
   else return ()) st = (INR exc,st') ==>
  ?err. exc = Error err
Proof
  Cases_on `nr` >> simp[return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  rw[acquire_nonreentrant_lock_def, bind_def, get_transient_storage_def,
     update_transient_def, return_def, raise_def] >> gvs[AllCaseEqs()]
QED

(* A committed halt, ordinary fall-through, or return must reach the body:
   the lock and incoming-value setup can only raise an Error. *)
Theorem call_prefix_terminal_body_result_cases:
  (!exc st'. lock_action st = (INR exc,st') ==> ?err. exc = Error err) /\
  (do lock_action; send_call_value mut cx; eval_stmts cx body od) st =
    (res,body_st') /\
  (res = INL () \/ (?v. res = INR (ReturnException v)) \/ res = INR HaltException) ==>
  ?lock_st body_st.
    lock_action st = (INL (),lock_st) /\
    send_call_value mut cx lock_st = (INL (),body_st) /\
    eval_stmts cx body body_st = (res,body_st')
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  imp_res_tac send_call_value_error >> gvs[] >> metis_tac[]
QED

Theorem call_lock_send_success_components:
  machine_well_typed am /\ scope_well_typed scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (INL (),lock_st) /\
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
     qexistsl [`cx`, `gobs`, `mut`, `nr`, `orc`, `rqs`] >> simp[bind_def, ignore_bind_def]) >>
  `lock_st.accounts =
     (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>).accounts` by
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
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (INL (),lock_st) /\
  send_call_value mut cx lock_st = (INL (),body_st) /\
  eval_stmts cx body body_st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >> vyperSourceSupplyLib.forward >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `body_st.scopes = [scope] /\ body_st.immutables = am.immutables /\
   state_well_typed body_st /\ accounts_well_typed body_st.accounts` by
    (irule call_lock_send_success_components >> simp[] >>
     qexistsl [`cx`, `gobs`, `lock_st`, `mut`, `nr`, `orc`, `rqs`] >> simp[]) >>
  `ALL_DISTINCT (MAP FST args)` by
    (`check_function_body am.layouts tx.target mods art src External mut nr
       args dflts ret body` by
       (irule check_contract_runtime_function_body_MEM >> simp[] >>
        qexistsl [`tx.function_name`, `raw`] >> simp[]) >>
     gvs[check_function_body_def, params_ok_def]) >>
  irule checked_explicit_external_body_preserves_machine_components >>
  qexistsl [`am`, `args`, `art`, `body`, `cx`, `dflts`, `mods`, `mut`, `nr`,
            `raw`, `res`, `ret`, `scope`, `src`, `body_st`, `ts`, `tx`, `vals`] >>
  simp[]
QED

Theorem checked_getter_body_from_states_preserves_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (INL (),lock_st) /\
  send_call_value mut cx lock_st = (INL (),body_st) /\
  eval_stmts cx body body_st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >> vyperSourceSupplyLib.forward >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `body_st.scopes = [scope] /\ body_st.immutables = am.immutables /\
   state_well_typed body_st /\ accounts_well_typed body_st.accounts` by
    (irule call_lock_send_success_components >> simp[] >>
     qexistsl [`cx`, `gobs`, `lock_st`, `mut`, `nr`, `orc`, `rqs`] >> simp[]) >>
  irule checked_public_getter_body_preserves_machine_components >>
  simp[] >> metis_tac[]
QED

Theorem checked_getter_send_eval_success_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (View,nr,args,[],ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (do send_call_value View cx; eval_stmts cx body
   od (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (res,st')) /\
  (res = INL () \/ (?v. res = INR (ReturnException v)) \/ res = INR HaltException) ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >> vyperSourceSupplyLib.forward >>
  Cases_on `cx.txn.value = 0` >>
  gvs[send_call_value_def, check_def, assert_def, raise_def,
      ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  irule checked_public_getter_body_preserves_machine_components >>
  goal_assum (drule_at (Pat `eval_stmts`)) >>
  goal_assum (drule_at (Pat `external_getter_tuple`)) >>
  gvs[initial_state_def, machine_well_typed_def, state_well_typed_def] >>
  metis_tac[]
QED


Theorem checked_explicit_call_run_success_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
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
   od (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (res,st')) /\
  (res = INL () \/ (?v. res = INR (ReturnException v)) \/ res = INR HaltException) ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  `?lock_st body_st.
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ())
       (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) =
         (INL (),lock_st) /\
     send_call_value mut cx lock_st = (INL (),body_st) /\
     eval_stmts cx body body_st = (res,st')` by
    (irule call_prefix_terminal_body_result_cases >> simp[] >>
     rpt strip_tac >> drule call_lock_action_error >> simp[]) >>
  `cx = initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
  drule_all checked_explicit_body_from_states_preserves_components >> simp[]
QED


Theorem checked_getter_call_run_components[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM decl ts /\ is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,(dflts : expr list),ret,body) /\
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
   od (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (res,st')) /\
  (res = INL () \/ (?v. res = INR (ReturnException v)) \/ res = INR HaltException) ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  `?lock_st body_st.
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ())
       (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) =
         (INL (),lock_st) /\
     send_call_value mut cx lock_st = (INL (),body_st) /\
     eval_stmts cx body body_st = (res,st')` by
    (irule call_prefix_terminal_body_result_cases >> simp[] >>
     rpt strip_tac >> drule call_lock_action_error >> simp[]) >>
  `cx = initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
  drule_all checked_getter_body_from_states_preserves_components >> simp[]
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
  ~cx.in_deploy /\ exc <> HaltException /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INR exc,am',rqs) ==>
  am' = am
Proof
  strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def] >>
  IF_CASES_TAC >- simp[] >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>)` >>
  Cases_on `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>)` >>
  Cases_on `q` >> simp_tac (srw_ss()) []
  >- (rpt (BasicProvers.TOP_CASE_TAC >> simp_tac (srw_ss()) []) >> metis_tac[]) >>
  Cases_on `y` >> simp_tac (srw_ss()) [] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp_tac (srw_ss()) []) >> metis_tac[]
QED

Theorem call_external_function_initial_failure_rolls_back:
  call_external_function orc gobs am
    (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (INR exc,am',rqs) /\
  exc <> HaltException ==>
  am' = am
Proof
  strip_tac >>
  `~(initial_evaluation_context am.sources am.layouts tx src).in_deploy` by
    simp[initial_evaluation_context_def] >>
  drule_all call_external_function_nondeploy_failure_rolls_back >> simp[]
QED

Theorem call_external_failure_rolls_back:
  call_external orc gobs am tx = (INR exc,am',rqs) /\ exc <> HaltException ==> am' = am
Proof
  rw[call_external_def] >> gvs[AllCaseEqs()] >>
  drule (call_external_function_initial_failure_rolls_back |>
    PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >> simp[]
QED

Theorem release_action_result:
  (if nr /\ ~is_view then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==> res = INL ()
Proof
  Cases_on `nr /\ ~is_view` >> simp[return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp[release_nonreentrant_lock_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def]
QED

(* Exact committed-halt branch, shared by calls and constructor execution. *)
Theorem call_external_function_halt_cases:
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INR HaltException,am_out,rqs) ==>
  ?am_c st_halt.
    (if cx.in_deploy then evaluate_all_constants cx am cx.txn.target mods
     else SOME am) = SOME am_c /\
    (do
      send_call_value mut cx;
      dflt_vs <- eval_external_defaults cx
        (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => do
          set_scopes [env];
          (if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                              (mut = View \/ mut = Pure)
           else return ());
          eval_stmts cx body
        od
    od) (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs|>) = (INR HaltException,st_halt) /\
    am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_halt /\
    rqs = st_halt.requests
Proof
  strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `(do
      send_call_value mut cx;
      dflt_vs <- eval_external_defaults cx
        (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => do
          set_scopes [env];
          (if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                              (mut = View \/ mut = Pure)
           else return ());
          eval_stmts cx body
        od
    od) (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs|>)` >>
  rename1 `(do
      send_call_value mut cx;
      dflt_vs <- eval_external_defaults cx
        (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts);
      case bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => do
          set_scopes [env];
          (if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                              (mut = View \/ mut = Pure)
           else return ());
          eval_stmts cx body
        od
    od) (initial_state am_c [FEMPTY] with
      <|outcomes := orc; requests := []; gas_obs := gobs|>) = (pipeline_result,pipeline_state)` >>
  Cases_on `pipeline_result` >> gvs[AllCaseEqs()] >>
  Cases_on `(if nr /\ mut <> View /\ mut <> Pure then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) pipeline_state` >>
  rename1 `(if _ then _ else _) _ = (unlock_result,unlocked_state)` >>
  Cases_on `unlock_result` >> gvs[AllCaseEqs()] >>
  imp_res_tac (release_action_result |> SPEC_ALL |>
    Q.INST [`is_view` |-> `mut = View \/ mut = Pure`] |> SRULE []) >> gvs[] >>
  rename1 `_ = (INR body_exc,body_state)` >>
  Cases_on `body_exc` >> gvs[triple_identity, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem checked_call_external_failure_preserves_machine_well_typed:
  machine_well_typed am /\ call_external orc gobs am tx = (INR exc,am',rqs) /\
  exc <> HaltException ==>
  machine_well_typed am'
Proof
  metis_tac[call_external_failure_rolls_back]
QED

(* Concrete-state interface for the complete explicit entry pipeline. *)
Theorem checked_explicit_initial_entry_components[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  (do
    send_call_value mut cx;
    dvs <- eval_external_defaults cx (DROP k dflts);
    case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
      NONE => raise (Error (RuntimeError "call bind_arguments"))
    | SOME scope => do
        set_scopes [scope];
        (if nr then
           case cx.nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                            (mut = View \/ mut = Pure)
         else return ());
        eval_stmts cx body
      od
  od) (initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gobs|>) = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed cx` by
    gvs[call_tx_well_typed_def, context_well_typed_def,
        initial_evaluation_context_def] >>
  `state_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>) /\
   accounts_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>).accounts` by
    gvs[initial_state_def, state_well_typed_def, machine_well_typed_def, scope_well_typed_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>).immutables` by
    (simp_tac (srw_ss()) [initial_state_def] >>
     metis_tac[checked_contract_runtime_ready_def,
               immutables_ready_initial_evaluation_context_source]) >>
  drule_all checked_external_entry_sound >> simp[]
QED

(* ===== Successful selected entries ===== *)

Theorem call_external_function_selected_explicit_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_well_typed am'
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed cx` by
    gvs[call_tx_well_typed_def, context_well_typed_def,
        initial_evaluation_context_def] >>
  `state_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>) /\
   accounts_well_typed (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>).accounts` by
    gvs[initial_state_def, state_well_typed_def, machine_well_typed_def, scope_well_typed_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx
    (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>).immutables` by
    (simp_tac (srw_ss()) [initial_state_def] >>
     metis_tac[checked_contract_runtime_ready_def,
               immutables_ready_initial_evaluation_context_source]) >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [call_external_function_def, LET_THM] >>
  `cx.in_deploy = F` by simp[initial_evaluation_context_def] >>
  qpat_assum `cx.in_deploy = F` (fn th => pure_rewrite_tac [th, COND_CLAUSES]) >>
  IF_CASES_TAC >- gvs[] >>
  simp_tac (srw_ss()) [] >>
  qmatch_goalsub_abbrev_tac `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>)` >>
  Cases_on `entry (initial_state am [FEMPTY] with <|outcomes := orc; requests := []; gas_obs := gobs|>)` >>
  rename1 `entry _ = (entry_res,st_body)` >>
  `state_well_typed st_body /\ accounts_well_typed st_body.accounts` by
    (qpat_x_assum `entry _ = _` mp_tac >>
     simp_tac bool_ss [Abbr `entry`] >> strip_tac >>
     drule_all checked_explicit_initial_entry_components >> simp[]) >>
  namedCases_on `entry_res` ["entry_unit", "entry_exc"] >> simp[]
  >- (Cases_on `entry_unit` >> simp[] >> strip_tac >>
      qmatch_asmsub_abbrev_tac `pair_CASE unlocked` >>
      PairCases_on `unlocked` >> Cases_on `unlocked0` >> gvs[] >>
      irule release_action_success_machine_well_typed >>
      qexistsl [`initial_evaluation_context am.sources am.layouts tx src`,
                `mut = View \/ mut = Pure`, `nr`, `st_body`] >>
      gvs[DE_MORGAN_THM]) >>
  Cases_on `entry_exc` >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `pair_CASE unlocked` >>
  PairCases_on `unlocked` >> Cases_on `unlocked0` >> gvs[] >>
  Cases_on `evaluate_type (type_env_all_modules mods) ret` >> gvs[] >>
  rename1 `safe_cast return_ty return_value` >>
  Cases_on `safe_cast return_ty return_value` >> gvs[] >>
  irule release_action_success_machine_well_typed >>
  qexistsl [`initial_evaluation_context am.sources am.layouts tx src`,
            `mut = View \/ mut = Pure`, `nr`, `st_body`] >>
  gvs[DE_MORGAN_THM]
QED

Theorem checked_getter_initial_body_components:
  eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
    (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) = (res,st') ==>
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,(dflts : expr list),ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `state_well_typed (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>) /\
   accounts_well_typed (initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>).accounts` by
    gvs[initial_state_def, state_well_typed_def, machine_well_typed_def] >>
  gvs[initial_state_def] >>
  drule_all (Q.INST
    [`cx` |-> `initial_evaluation_context am.sources am.layouts tx src`,
     `st` |-> `initial_state am [scope] with <|outcomes := orc; requests := rqs; gas_obs := gobs|>`]
    (SPEC_ALL checked_public_getter_body_preserves_machine_components)
    |> SIMP_RULE (srw_ss()) [initial_state_def] |> GEN_ALL) >>
  simp[]
QED

Theorem call_external_function_selected_explicit_halt_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INR HaltException,am',rqs) ==>
  machine_well_typed am'
Proof
  strip_tac >>
  `~cx.in_deploy` by simp[initial_evaluation_context_def] >>
  drule call_external_function_halt_cases >> strip_tac >> gvs[] >>
  `initial_evaluation_context am.sources am.layouts tx src =
     initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
  `state_well_typed st_halt /\ accounts_well_typed st_halt.accounts` by
    (drule_all checked_explicit_initial_entry_components >> simp[]) >>
  irule abstract_machine_from_state_well_typed >>
  gvs[state_well_typed_def]
QED


Theorem checked_getter_initial_entry_components[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\ module_allocated am.layouts tx.target src ts /\
  MEM decl ts /\ is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  (res = INL () \/ (?v. res = INR (ReturnException v)) \/ res = INR HaltException) /\
  (do
    send_call_value mut cx;
    dvs <- eval_external_defaults cx (DROP k dflts);
    case bind_arguments (type_env_all_modules mods) args (vals ++ dvs) of
      NONE => raise (Error (RuntimeError "call bind_arguments"))
    | SOME scope => do
        set_scopes [scope];
        (if nr then
           case cx.nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                            (mut = View \/ mut = Pure)
         else return ());
        eval_stmts cx body
      od
  od) (initial_state am [FEMPTY] with
    <|outcomes := orc; requests := []; gas_obs := gobs|>) = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  `mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
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
  `nr ==> cx.nonreentrant_slot <> NONE` by
    (strip_tac >> drule_all checked_selected_getter_lock_slot >>
     simp[initial_evaluation_context_def]) >>
  gvs[] >>
  Cases_on `tx.value = 0` >>
  gvs[send_call_value_def, initial_evaluation_context_def,
      eval_external_defaults_nil, bind_def, ignore_bind_def, return_def,
      check_def, assert_def, raise_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `bind_arguments (type_env_all_modules mods) args vals` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, set_scopes_def,
      initial_state_def] >>
  qmatch_asmsub_abbrev_tac `eval_stmts ctx getter_body` >>
  qmatch_asmsub_abbrev_tac `(if nr then lock else return ()) entry_st` >>
  `(do lock_if_nr ctx nr T; eval_stmts ctx getter_body od) entry_st =
     eval_stmts ctx getter_body entry_st \/
   ?msg. (do lock_if_nr ctx nr T; eval_stmts ctx getter_body od) entry_st =
     (INR (Error (RuntimeError msg)),entry_st)` by
    (irule view_lock_prefix_execution >> simp[Abbr `ctx`]) >>
  gvs[lock_if_nr_def, bind_def, ignore_bind_def, Abbr `ctx`,
      Abbr `lock`, Abbr `entry_st`, Abbr `getter_body`] >>
  qpat_x_assum `(_,st') = eval_stmts _ _ _` (assume_tac o SYM) >>
  drule (SRULE [initial_evaluation_context_def, initial_state_def]
    checked_getter_initial_body_components) >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem call_external_function_selected_getter_success_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INL v,am',rqs) ==>
  machine_well_typed am'
Proof
  rpt strip_tac >>
  `mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
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
  `(nr ==> (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot <> NONE)` by
    (strip_tac >> drule_all checked_selected_getter_lock_slot >>
     simp[initial_evaluation_context_def]) >>
  dxrule_all_then assume_tac call_external_function_view_success_without_lock >>
  drule call_external_function_success_phases >> strip_tac >>
  gvs[eval_external_defaults_nil, bind_def, ignore_bind_def, return_def,
      initial_evaluation_context_def] >>
  qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
  simp[send_call_value_def, check_def, assert_def, bind_def, ignore_bind_def,
       return_def, raise_def] >>
  IF_CASES_TAC >> gvs[return_def, raise_def] >> strip_tac >>
  gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def,
      initial_state_def] >>
  `state_well_typed st_body /\ accounts_well_typed st_body.accounts` by
    (drule (SRULE [initial_state_def, initial_evaluation_context_def]
       checked_getter_initial_body_components) >>
     disch_then irule >> metis_tac[]) >>
  gvs[machine_well_typed_def, abstract_machine_from_state_def,
      state_well_typed_def]
QED

Theorem call_external_function_selected_getter_halt_machine_well_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\ machine_well_typed am /\ machine_supply am orc /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  LENGTH vals <= LENGTH args /\ LENGTH args - LENGTH vals <= LENGTH dflts /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret =
    (INR HaltException,am',rqs) ==>
  machine_well_typed am'
Proof
  strip_tac >>
  `~cx.in_deploy` by simp[initial_evaluation_context_def] >>
  drule call_external_function_halt_cases >> strip_tac >> gvs[] >>
  `initial_evaluation_context am.sources am.layouts tx src =
     initial_evaluation_context am.sources am.layouts tx src` by simp[] >>
  `state_well_typed st_halt /\ accounts_well_typed st_halt.accounts` by
    (drule_all (checked_getter_initial_entry_components |> SPEC_ALL |>
       Q.INST [`res` |-> `INR HaltException`] |> SRULE [] |> GEN_ALL) >> simp[]) >>
  irule abstract_machine_from_state_well_typed >>
  gvs[state_well_typed_def]
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
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  checked_external_call_inputs_ready am tx /\
  call_external orc gobs am tx = (INL v,am',rqs) ==>
  machine_well_typed am'
Proof
  rpt strip_tac >>
  `!ts. ALOOKUP mods (find_function_module am tx.target tx.function_name) = SOME ts ==>
        module_allocated am.layouts tx.target
          (find_function_module am tx.target tx.function_name) ts` by
    metis_tac[checked_contract_runtime_ready_module_allocated] >>
  qpat_x_assum `call_external orc gobs am tx = _` mp_tac >>
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
    gvs[checked_call_inputs_ready_def, checked_defaults_ready_def]
  >>~- ([`MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts`],
      drule_at (Pat `call_external_function`)
        call_external_function_selected_explicit_success_machine_well_typed >>
      simp[] >> disch_then (fn th => metis_tac[th])) >>
  (`mut = View /\ dflts = []` by
       (Cases_on `decl` >> gvs[is_public_getter_decl_def]
        >- (rename1 `is_public_getter_decl _ (VariableDecl vis storage id ty init)` >>
            Cases_on `vis` >> gvs[is_public_getter_decl_def] >>
            Cases_on `is_ArrayT ty`
            >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
            gvs[external_getter_tuple_def]) >>
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

Theorem checked_call_external_halt_preserves_machine_well_typed:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  checked_external_call_inputs_ready am tx /\
  call_external orc gobs am tx = (INR HaltException,am',rqs) ==>
  machine_well_typed am'
Proof
  rpt strip_tac >>
  `!ts. ALOOKUP mods (find_function_module am tx.target tx.function_name) = SOME ts ==>
        module_allocated am.layouts tx.target
          (find_function_module am tx.target tx.function_name) ts` by
    metis_tac[checked_contract_runtime_ready_module_allocated] >>
  qpat_x_assum `call_external orc gobs am tx = _` mp_tac >>
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
  `LENGTH tx.args <= LENGTH args /\
   LENGTH args - LENGTH tx.args <= LENGTH dflts` by
    gvs[checked_call_inputs_ready_def, checked_defaults_ready_def] >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  irule finalize_pending_deletions_machine_well_typed >>
  FIRST
    [qpat_assum `MEM (FunctionDecl External _ _ _ _ _ _ _ _) _` kall_tac >>
     drule_at (Pat `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
       call_external_function_selected_explicit_halt_machine_well_typed,
     qpat_assum `is_public_getter_decl _ _` kall_tac >>
     drule_at (Pat `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
       call_external_function_selected_getter_halt_machine_well_typed] >>
  simp[initial_evaluation_context_def, checked_contract_runtime_ready_def] >>
  disch_then irule >> metis_tac[]
QED

Theorem checked_call_external_preserves_machine_well_typed:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ machine_supply am orc /\ call_tx_well_typed tx /\
  checked_external_call_inputs_ready am tx /\
  call_external orc gobs am tx = (res,am',rqs) ==>
  machine_well_typed am'
Proof
  Cases_on `res` >> strip_tac
  >- metis_tac[checked_call_external_success_preserves_machine_well_typed] >>
  rename1 `call_external orc gobs am tx = (INR exc,am',rqs)` >>
  Cases_on `exc = HaltException` >> gvs[]
  >- metis_tac[checked_call_external_halt_preserves_machine_well_typed] >>
  metis_tac[checked_call_external_failure_preserves_machine_well_typed]
QED
