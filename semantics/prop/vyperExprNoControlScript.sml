Theory vyperExprNoControl

Ancestors
  pair vyperCreate vyperCreateFrame vyperInterpreter vyperAST vyperMisc
  vyperCallFrame vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches vyperCallOutcomeFrame
  vyperRuntimeAccounts vyperState
Libs
  pairLib monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);
val _ = hide "body";
val _ = overload_on ("bind", ``vyperState$bind``);
val _ = overload_on ("return", ``vyperState$return``);
val _ = overload_on ("ignore_bind", ``vyperState$ignore_bind``);
val _ = overload_on ("raise", ``vyperState$raise``);
val _ = overload_on ("try", ``vyperState$try``);
val _ = overload_on ("finally", ``vyperState$finally``);

(* ===== Helper predicate ===== *)
Definition no_control_exc_def:
  no_control_exc exc ⇔ (∃str. exc = Error str) ∨ (∃str. exc = AssertException str)
End

(* Useful rewrite set for pushing case expressions through application *)
val case_rator_ss = [option_CASE_rator, sum_CASE_rator, prod_CASE_rator, COND_RATOR]

(* ===== Monadic propagation lemmas ===== *)

Theorem bind_INR:
  ∀f g s exc s'.
  bind f g s = (INR exc, s') ⇒
  (f s = (INR exc, s') ∨
   ∃v s''. f s = (INL v, s'') ∧ g v s'' = (INR exc, s'))
Proof
  rpt gen_tac >> strip_tac >> fs[bind_def]
  >> pop_assum mp_tac >> CASE_TAC >> CASE_TAC
QED

Theorem bind_no_control:
  ∀f g s exc s'.
  bind f g s = (INR exc, s') ⇒
  (∀exc' s''. f s = (INR exc', s'') ⇒ no_control_exc exc') ⇒
  (∀v s'' exc' s'''. f s = (INL v, s'') ⇒ g v s'' = (INR exc', s''') ⇒ no_control_exc exc') ⇒
  no_control_exc exc
Proof
  rpt gen_tac >> simp[bind_def, prod_CASE_rator, sum_CASE_rator]
  >> strip_tac >> rpt disch_tac >> gvs[AllCaseEqs()]
QED

Theorem ignore_bind_INR:
  ∀f g s exc s'.
  ignore_bind f g s = (INR exc, s') ⇒
  (f s = (INR exc, s') ∨
   ∃v s''. f s = (INL v, s'') ∧ g s'' = (INR exc, s'))
Proof
  rpt gen_tac >> strip_tac >> fs[ignore_bind_def, bind_def]
  >> pop_assum mp_tac >> CASE_TAC >> CASE_TAC
QED

Theorem handle_function_no_control:
  ∀e s exc s'.
  handle_function e s = (INR exc, s') ⇒ no_control_exc exc
Proof
  Cases >> simp[handle_function_def, return_def, raise_def, no_control_exc_def]
QED

Theorem try_handle_function_no_control:
  ∀f s exc s'.
  try f handle_function s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[try_def, prod_CASE_rator, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> imp_res_tac handle_function_no_control
QED

Theorem finally_no_control:
  ∀f g s exc s'.
  finally f g s = (INR exc, s') ⇒
  (∀exc0 s0. f s = (INR exc0, s0) ⇒ no_control_exc exc0) ⇒
  (∀s0 exc0 s0'. g s0 = (INR exc0, s0') ⇒ no_control_exc exc0) ⇒
  no_control_exc exc
Proof
  rpt gen_tac >> simp[finally_def, ignore_bind_def, bind_def,
    prod_CASE_rator, sum_CASE_rator, raise_def]
  >> strip_tac >> rpt disch_tac
  >> gvs[AllCaseEqs(), raise_def, return_def] >> res_tac
QED

Theorem switch_BoolV_no_control:
  ∀v f g s exc s'.
  switch_BoolV v f g s = (INR exc, s') ⇒
  (∀exc' s''. f s = (INR exc', s'') ⇒ no_control_exc exc') ⇒
  (∀exc' s''. g s = (INR exc', s'') ⇒ no_control_exc exc') ⇒
  no_control_exc exc
Proof
  simp[switch_BoolV_def] >> rw[] >> gvs[raise_def, no_control_exc_def]
QED

(* ===== Helper function exception lemmas ===== *)

Theorem check_no_control:
  ∀b str s exc s'.
  check b str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[check_def, assert_def, no_control_exc_def]
QED

Theorem type_check_no_control:
  ∀b str s exc s'.
  type_check b str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[type_check_def, assert_def, no_control_exc_def]
QED

Theorem lift_option_no_control:
  ∀x str s exc s'.
  lift_option x str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_option_def, option_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem lift_option_type_no_control:
  ∀x str s exc s'.
  lift_option_type x str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_option_type_def, option_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem lift_sum_no_control:
  ∀x s exc s'.
  lift_sum x s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_sum_def, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem lift_sum_runtime_no_control:
  ∀x s exc s'.
  lift_sum_runtime x s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_sum_runtime_def, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem get_Value_no_control:
  ∀tv s exc s'.
  get_Value tv s = (INR exc, s') ⇒ no_control_exc exc
Proof
  Cases >> simp[get_Value_def, return_def, raise_def, no_control_exc_def]
QED

Theorem read_storage_slot_no_control:
  ∀cx is_t slot tv s exc s'.
  read_storage_slot cx is_t slot tv s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[read_storage_slot_def, bind_def,
    get_storage_backend_def, get_transient_storage_def,
    get_accounts_def, return_def, prod_CASE_rator, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs()]
  >- imp_res_tac lift_option_no_control
  >> (Cases_on `is_t`
      >> fs[get_storage_backend_def, bind_def, get_transient_storage_def,
            get_accounts_def, return_def])
QED

Theorem materialise_no_control:
  ∀cx tv s exc s'.
  materialise cx tv s = (INR exc, s') ⇒ no_control_exc exc
Proof
  gen_tac >> Cases >> rpt gen_tac
  >> simp[materialise_def, bind_def, return_def, raise_def, no_control_exc_def]
  >> strip_tac >> gvs[AllCaseEqs(), return_def]
  >> imp_res_tac read_storage_slot_no_control >> gvs[no_control_exc_def]
QED

Theorem return_not_INR[simp]:
  return v s ≠ (INR exc, s')
Proof
  simp[return_def]
QED

Theorem raise_no_control:
  ∀exc s exc' s'.
  raise exc s = (INR exc', s') ⇒ exc' = exc
Proof
  simp[raise_def]
QED

(* ===== Additional helpers for common patterns ===== *)

Theorem toplevel_array_length_no_control:
  ∀cx tv s exc s'.
  toplevel_array_length cx tv s = (INR exc, s') ⇒ no_control_exc exc
Proof
  ho_match_mp_tac toplevel_array_length_ind >> rpt strip_tac
  >> gvs[toplevel_array_length_def, return_def, raise_def, no_control_exc_def,
         bind_def, get_storage_backend_def, get_transient_storage_def,
         get_accounts_def]
  >> pop_assum mp_tac
  >> CASE_TAC >> CASE_TAC
  >> Cases_on `is_transient`
  >> gvs[get_storage_backend_def, get_transient_storage_def, get_accounts_def,
         bind_def, return_def]
QED

Theorem check_array_bounds_no_control:
  ∀cx tv v s exc s'.
  check_array_bounds cx tv v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  ho_match_mp_tac check_array_bounds_ind >> rpt strip_tac
  >> gvs[check_array_bounds_def, return_def, bind_def,
         get_storage_backend_def, get_transient_storage_def,
         get_accounts_def, AllCaseEqs()]
  >> Cases_on `is_transient`
  >> gvs[get_storage_backend_def, bind_def, get_transient_storage_def,
         get_accounts_def, return_def]
  >> imp_res_tac check_no_control
QED

Theorem transfer_value_no_control:
  ∀from to amt s exc s'.
  transfer_value from to amt s = (INR exc, s') ⇒ no_control_exc exc
Proof
  (* Original concrete implementation proof:
  rpt gen_tac >>
  rename1 `transfer_value fromAddr toAddr amount st = (INR exc, st') ⇒ no_control_exc exc` >>
  Cases_on `amount = 0 ∨ fromAddr = toAddr`
  >- simp[transfer_value_def, return_def]
  >> simp[transfer_value_def, bind_def, ignore_bind_def,
    get_accounts_def, return_def, update_accounts_def]
  >> strip_tac >> gvs[AllCaseEqs(), return_def]
  >> imp_res_tac check_no_control
  *)
  rpt strip_tac >> drule concrete_send_error >> rw[no_control_exc_def]
QED

Theorem get_immutables_no_control:
  ∀cx src s exc s'.
  get_immutables cx src s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac
  >> simp[get_immutables_def, get_address_immutables_def,
          bind_def, get_accounts_def, return_def, prod_CASE_rator, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> imp_res_tac lift_option_type_no_control
QED

Theorem lookup_global_no_control:
  ∀cx src n s exc s'.
  lookup_global cx src n s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> strip_tac
  >> pop_assum mp_tac
  >> simp[lookup_global_def, bind_def, prod_CASE_rator, sum_CASE_rator,
          option_CASE_rator, toplevel_value_CASE_rator, var_decl_info_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> TRY (imp_res_tac lift_option_type_no_control >> NO_TAC)
  >> TRY (imp_res_tac read_storage_slot_no_control >> NO_TAC)
  >> TRY (gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
      >> TRY (imp_res_tac get_immutables_no_control >> gvs[no_control_exc_def])
      >> NO_TAC)
  (* StorageVarDecl remaining: case on tv *)
  >> Cases_on `tv`
  >> gvs[bind_def, prod_CASE_rator, sum_CASE_rator, return_def, AllCaseEqs()]
  >> imp_res_tac read_storage_slot_no_control
QED

Theorem lookup_flag_mem_no_control:
  ∀cx nsid mid s exc s'.
  lookup_flag_mem cx nsid mid s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> Cases_on `nsid` >> strip_tac
  >> pop_assum mp_tac
  >> simp[lookup_flag_mem_def, option_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem acquire_nonreentrant_lock_no_control:
  ∀addr slot is_v s exc s'.
  acquire_nonreentrant_lock addr slot is_v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[acquire_nonreentrant_lock_def, bind_def,
    get_transient_storage_def, return_def]
  >> rw[raise_def, no_control_exc_def, update_transient_def, return_def]
QED

Theorem push_log_no_control:
  ∀log s exc s'.
  push_log log s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[push_log_def, return_def]
QED

Theorem append_logs_no_control:
  ∀logs s exc s'.
  append_logs logs s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[append_logs_def, return_def]
QED

Theorem write_storage_slot_no_control:
  ∀cx is_t slot tv v s exc s'.
  write_storage_slot cx is_t slot tv v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> strip_tac >> pop_assum mp_tac
  >> PURE_REWRITE_TAC[write_storage_slot_def]
  >> simp[bind_def, return_def, prod_CASE_rator, sum_CASE_rator, LET_THM,
    get_storage_backend_def, set_storage_backend_def,
    get_accounts_def, get_transient_storage_def,
    update_accounts_def, update_transient_def]
  >> strip_tac
  >> Cases_on `is_t`
  >> gvs[AllCaseEqs(), get_storage_backend_def, set_storage_backend_def,
         get_accounts_def, get_transient_storage_def,
         update_accounts_def, update_transient_def,
         bind_def, return_def, prod_CASE_rator, sum_CASE_rator]
  >> imp_res_tac lift_option_type_no_control
QED

Theorem assign_result_no_control:
  ∀tv ao old_val subs s exc s'.
  assign_result tv ao old_val subs s = (INR exc, s') ⇒ no_control_exc exc
Proof
  Cases_on `ao` >> simp[assign_result_def, return_def, bind_def,
    prod_CASE_rator, sum_CASE_rator]
  >> rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()]
  >> imp_res_tac lift_sum_no_control
QED

Theorem set_global_no_control:
  ∀cx src n v s exc s'.
  set_global cx src n v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> strip_tac >> pop_assum mp_tac
  >> simp[set_global_def, bind_def, return_def, raise_def,
          prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
          COND_RATOR, LET_THM, var_decl_info_CASE_rator,
          no_control_exc_def]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> TRY (imp_res_tac lift_option_type_no_control >> gvs[no_control_exc_def] >> NO_TAC)
  >> TRY (imp_res_tac write_storage_slot_no_control >> gvs[no_control_exc_def] >> NO_TAC)
QED

Theorem set_immutable_no_control:
  ∀cx src n tv v s exc s'.
  set_immutable cx src n tv v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[set_immutable_def, bind_def, return_def,
    LET_THM, get_address_immutables_def, set_address_immutables_def,
    prod_CASE_rator, sum_CASE_rator, option_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> imp_res_tac lift_option_type_no_control
QED

Theorem resolve_array_element_no_control:
  ∀cx is_t slot tv subs s exc s'.
  resolve_array_element cx is_t slot tv subs s = (INR exc, s') ⇒
  no_control_exc exc
Proof
  ho_match_mp_tac resolve_array_element_ind >> rpt conj_tac >> rpt gen_tac
  (* IntSubscript case - recursive *)
  >- (
    disch_tac >> rpt gen_tac >> strip_tac
    >> pop_assum mp_tac >> PURE_REWRITE_TAC[Once resolve_array_element_def]
    >> simp[bind_def, ignore_bind_def, return_def, raise_def,
      prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
      COND_RATOR, LET_THM,
      get_storage_backend_def, get_transient_storage_def,
      get_accounts_def]
    >> strip_tac >> gvs[AllCaseEqs()]
    >> TRY (res_tac >> NO_TAC)
    >> Cases_on `bd`
    >> gvs[bind_def, return_def, raise_def,
           get_storage_backend_def, get_transient_storage_def,
           get_accounts_def, prod_CASE_rator, sum_CASE_rator, AllCaseEqs()]
    >> imp_res_tac check_no_control >> gvs[]
    >> Cases_on `is_t`
    >> gvs[get_storage_backend_def, bind_def,
           get_transient_storage_def, get_accounts_def, return_def])
  (* All other cases: non-recursive, simple *)
  >> (rpt (gen_tac ORELSE disch_then strip_assume_tac)
      >> gvs[Once resolve_array_element_def, return_def, raise_def,
             no_control_exc_def])
QED

val at_helpers = [lift_option_no_control, lift_option_type_no_control,
  lift_sum_no_control, check_no_control, type_check_no_control,
  write_storage_slot_no_control, assign_result_no_control,
  read_storage_slot_no_control, lookup_global_no_control,
  set_global_no_control, set_immutable_no_control,
  get_immutables_no_control, resolve_array_element_no_control];

val at_mono = [bind_def, ignore_bind_def, return_def, raise_def,
  prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
  toplevel_value_CASE_rator,
  vyperValueTheory.type_value_CASE_rator,
  vyperStateTheory.assign_operation_CASE_rator,
  vyperASTTheory.bound_CASE_rator,
  COND_RATOR, LET_THM, get_scopes_def, set_scopes_def,
  no_control_exc_def];

(* Fast resolution for common assign_target branches before the broader search. *)
val at_resolve_quick = FIRST [
  qpat_x_assum `assign_result _ _ _ _ _ = (INR _, _)`
    (mp_tac o MATCH_MP assign_result_no_control) >> gvs[no_control_exc_def] >> NO_TAC,
  qpat_x_assum `lift_sum _ _ = (INR _, _)`
    (mp_tac o MATCH_MP lift_sum_no_control) >> gvs[no_control_exc_def] >> NO_TAC,
  qpat_x_assum `read_storage_slot _ _ _ _ _ = (INR _, _)`
    (mp_tac o MATCH_MP read_storage_slot_no_control) >> gvs[no_control_exc_def] >> NO_TAC,
  qpat_x_assum `write_storage_slot _ _ _ _ _ _ = (INR _, _)`
    (mp_tac o MATCH_MP write_storage_slot_no_control) >> gvs[no_control_exc_def] >> NO_TAC,
  qpat_x_assum `lift_option_type _ _ _ = (INR _, _)`
    (mp_tac o MATCH_MP lift_option_type_no_control) >> gvs[no_control_exc_def] >> NO_TAC,
  qpat_x_assum `lookup_global _ _ _ _ = (INR _, _)`
    (mp_tac o MATCH_MP lookup_global_no_control) >> gvs[no_control_exc_def] >> NO_TAC
];

(* Resolution: try each helper, closing the goal completely *)
val at_resolve = FIRST (
  map (fn th => imp_res_tac th >> gvs[no_control_exc_def] >> NO_TAC) at_helpers
  @ [res_tac >> gvs[no_control_exc_def] >> NO_TAC,
     gvs[no_control_exc_def] >> NO_TAC]);

val assign_target_no_control_tac =
  let
    val gsb_contra =
      qpat_x_assum `get_storage_backend _ _ _ = (INR _, _)`
        (fn th => let val b = th |> concl |> lhs |> rator |> rand
          in assume_tac th >> Cases_on [ANTIQUOTE b]
             >> gvs[get_storage_backend_def, bind_def,
                    get_transient_storage_def, get_accounts_def, return_def]
          end)
    val step =
      gvs[pairTheory.ELIM_UNCURRY]
      >> gvs(AllCaseEqs() :: no_control_exc_def :: at_mono)
      >> TRY at_resolve_quick >> TRY at_resolve >> TRY gsb_contra
  in
    rpt gen_tac
    >> rpt (gen_tac ORELSE disch_then strip_assume_tac)
    >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[assign_target_def]
    >> simp at_mono >> strip_tac >> gvs[AllCaseEqs()]
    >> TRY at_resolve_quick >> TRY at_resolve >> step >> step
  end;

Theorem assign_target_no_control:
  (∀cx tv op s exc s'.
    assign_target cx tv op s = (INR exc, s') ⇒ no_control_exc exc) ∧
  (∀cx tvs vs s exc s'.
    assign_targets cx tvs vs s = (INR exc, s') ⇒ no_control_exc exc)
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac
  >- assign_target_no_control_tac
  >- (
    rpt gen_tac
    >> rpt (gen_tac ORELSE disch_then strip_assume_tac)
    >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[assign_target_def]
    >> simp at_mono >> strip_tac >> gvs[AllCaseEqs()]
    >> TRY at_resolve_quick >> TRY at_resolve
    >> gvs[pairTheory.ELIM_UNCURRY]
    >> gvs(AllCaseEqs() :: no_control_exc_def :: at_mono)
    >> TRY at_resolve_quick >> TRY at_resolve
    >> TRY (qpat_x_assum `get_storage_backend _ _ _ = (INR _, _)`
        (fn th => let val b = th |> concl |> lhs |> rator |> rand
          in assume_tac th >> Cases_on [ANTIQUOTE b]
             >> gvs[get_storage_backend_def, bind_def,
                    get_transient_storage_def, get_accounts_def, return_def]
          end))
    >> gvs[pairTheory.ELIM_UNCURRY]
    >> gvs(AllCaseEqs() :: no_control_exc_def :: at_mono)
    >> TRY at_resolve_quick >> TRY at_resolve
    >> TRY (qpat_x_assum `get_storage_backend _ _ _ = (INR _, _)`
        (fn th => let val b = th |> concl |> lhs |> rator |> rand
          in assume_tac th >> Cases_on [ANTIQUOTE b]
             >> gvs[get_storage_backend_def, bind_def,
                    get_transient_storage_def, get_accounts_def, return_def]
          end)))
  >> assign_target_no_control_tac
QED
(* ===== Shared tactic definitions ===== *)

val mono = [bind_def, ignore_bind_def, return_def, raise_def,
            prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            COND_RATOR, LET_THM,
            get_scopes_def, get_accounts_def, get_transient_storage_def,
            update_accounts_def, update_transient_def];

Theorem eval_create_no_control[local]:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (INR ex, st') ==>
  no_control_exc ex
Proof
  strip_tac >> drule eval_create_exception_is_error >> simp[no_control_exc_def]
QED

Theorem check_create_blueprint_no_control[local]:
  check_create_blueprint has_salt vs st = (INR ex, st') ==>
  no_control_exc ex
Proof
  strip_tac >> drule check_create_blueprint_exception_is_error >>
  simp[no_control_exc_def]
QED

val helpers = [eval_create_no_control, check_create_blueprint_no_control,
               check_no_control, type_check_no_control,
               lift_option_no_control, lift_option_type_no_control,
               lift_sum_no_control, lift_sum_runtime_no_control,
               get_Value_no_control, read_storage_slot_no_control,
               materialise_no_control, toplevel_array_length_no_control,
               check_array_bounds_no_control, transfer_value_no_control,
               acquire_nonreentrant_lock_no_control,
               handle_function_no_control, push_log_no_control,
               get_immutables_no_control, lookup_global_no_control,
               lookup_flag_mem_no_control, assign_target_no_control,
               write_storage_slot_no_control, assign_result_no_control,
               try_handle_function_no_control];

val resolve_tac = rpt (FIRST [
  res_tac >> gvs[no_control_exc_def] >> NO_TAC,
  gvs[no_control_exc_def] >> NO_TAC,
  qpat_x_assum `_ = (INL x, _)` (fn th =>
    Cases_on [ANTIQUOTE (th |> concl |> lhs |> rand |> rator |> rand)]
    >> gvs[] >> res_tac >> gvs[no_control_exc_def] >> NO_TAC),
  qpat_x_assum `switch_BoolV _ _ _ _ = (INR _, _)` (fn th =>
    assume_tac th
    >> drule switch_BoolV_no_control >> disch_then irule
    >> rpt strip_tac >> res_tac >> gvs[no_control_exc_def] >> NO_TAC),
  FIRST (map (fn th => imp_res_tac th >> gvs[no_control_exc_def] >> NO_TAC) helpers)
]);

fun unfold_tac g = (
  rpt strip_tac >> pop_assum mp_tac
  >> PURE_REWRITE_TAC[Once evaluate_def]
  >> simp mono >> strip_tac
  >> gvs[AllCaseEqs(), pairTheory.ELIM_UNCURRY] >> resolve_tac) g;

val bind_step_tac =
  qpat_x_assum `bind _ _ _ = (INR _, _)`
    (strip_assume_tac o MATCH_MP bind_INR) >> gvs[return_def, raise_def];
val ibind_step_tac =
  qpat_x_assum `ignore_bind _ _ _ = (INR _, _)`
    (strip_assume_tac o MATCH_MP ignore_bind_INR) >> gvs[return_def, raise_def];
val step_tac = FIRST [bind_step_tac, ibind_step_tac];

val helper_close = FIRST [
  gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def,
      get_accounts_def, get_transient_storage_def,
      update_accounts_def, update_transient_def,
      get_scopes_def, push_function_def] >> NO_TAC,
  gvs[no_control_exc_def, return_def, raise_def] >> NO_TAC,
  FIRST (map (fn th => imp_res_tac th >> gvs[no_control_exc_def] >> NO_TAC)
    helpers)
];

(* Direct exception closers avoid the context-wide search performed by
   imp_res_tac, which is expensive in the IntCall case. *)
val close_type_check =
  qpat_x_assum `type_check _ _ _ = (INR _, _)`
    (ACCEPT_TAC o MATCH_MP type_check_no_control);
val close_lift_option_type =
  qpat_x_assum `lift_option_type _ _ _ = (INR _, _)`
    (ACCEPT_TAC o MATCH_MP lift_option_type_no_control);

(* ===== Case 18: ExtCall and Send ===== *)

val CALL_NO_CONTROL_STEP = FIRST [
  step_tac,
  qpat_x_assum `append_logs _ _ = (INR _,_)`
    (ACCEPT_TAC o MATCH_MP append_logs_no_control),
  qpat_x_assum `take_call_outcome _ _ _ _ = (INR _,_)`
    (fn th => mp_tac (MATCH_MP take_call_outcome_error th)) >>
    simp[no_control_exc_def] >> strip_tac >> gvs[no_control_exc_def],
  qpat_x_assum `adopt_call_outcome _ _ _ = (INR _,_)` mp_tac >>
    simp[adopt_call_outcome_equation],
  helper_close,
  CHANGED_TAC (gvs[LET_THM, UNCURRY]),
  qpat_x_assum `_ = (INR _,_)` mp_tac >>
    BasicProvers.TOP_CASE_TAC >> simp[] >> strip_tac];

Theorem eval_ext_call_no_control:
  eval_ext_call cx static skip_check sig opts vs st = (INR exc, st') ==>
  no_control_exc exc
Proof
  PairCases_on `sig` >> Cases_on `vs` >>
  simp_tac bool_ss [eval_ext_call_def, eval_ext_call_effects_def, LET_THM] >> strip_tac >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  NTAC 4 (TRY CALL_NO_CONTROL_STEP) >> NTAC 4 (TRY CALL_NO_CONTROL_STEP) >>
  rpt CALL_NO_CONTROL_STEP
QED

Theorem eval_send_no_control:
  eval_send cx has_gas vs st = (INR exc, st') ==> no_control_exc exc
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def, no_control_exc_def] >>
  Cases_on `t` >- simp[eval_send_def, raise_def, no_control_exc_def] >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       return_def, raise_def, get_accounts_def, get_transient_storage_def,
       lift_option_def, lift_option_type_def, check_def, update_accounts_def,
       update_transient_def, append_logs_def,
       take_call_outcome_def, adopt_call_outcome_def, LET_THM, UNCURRY,
       COND_RATOR, option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), no_control_exc_def]
QED

(* ===== Case 19: IntCall ===== *)

(* Sub-helper: cleanup block never errors *)
Theorem int_call_cleanup_no_INR[local]:
  ∀prev b cx s exc s'.
  (do
    pop_function prev;
    if b then
      case cx.nonreentrant_slot of
        NONE => return ()
      | SOME slot => release_nonreentrant_lock cx.txn.target slot
    else return ()
  od) s = (INR exc, s') ⇒ F
Proof
  rpt gen_tac
  >> simp[pop_function_def, set_scopes_def, ignore_bind_def, bind_def,
     return_def, prod_CASE_rator, sum_CASE_rator, COND_RATOR,
     option_CASE_rator, release_nonreentrant_lock_def,
     get_transient_storage_def, update_transient_def]
  >> rpt (CASE_TAC >> gvs[])
QED

(* Sub-helper: tail after both eval_exprs calls *)
Theorem int_call_tail_no_control[local]:
  ∀all_tenv args vs dflt_vs ret prev is_view nr src_id_opt fn cx body s exc st'.
  (do
    env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
             "IntCall bind_arguments";
    rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ());
    cxf <- push_function (src_id_opt, fn) env cx;
    rv <- finally
      (try (do eval_stmts cxf body; return NoneV od) handle_function)
      (do pop_function prev;
          if nr ∧ ¬is_view then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od);
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return $ Value crv
  od) s = (INR exc, st') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> strip_tac
  >> rpt (step_tac >- FIRST [
    FIRST (map (fn th => imp_res_tac th >> gvs[no_control_exc_def] >> NO_TAC)
      [lift_option_type_no_control, acquire_nonreentrant_lock_no_control]),
    gvs[no_control_exc_def, return_def, raise_def,
        get_scopes_def, push_function_def] >> NO_TAC,
    Cases_on `nr` >> gvs[return_def, raise_def, option_CASE_rator,
      AllCaseEqs(), no_control_exc_def]
    >> TRY (imp_res_tac acquire_nonreentrant_lock_no_control
            >> gvs[no_control_exc_def]) >> NO_TAC,
    drule finally_no_control >> disch_then irule >> rpt strip_tac
    >> TRY (imp_res_tac try_handle_function_no_control >> NO_TAC)
    >> TRY (imp_res_tac int_call_cleanup_no_INR >> NO_TAC)])
QED

Theorem int_call_no_control[local]:
  ∀cx v16 src_id_opt fn es v17.
  (∀s'' x t s'3 ts t' s'4 tup t'' s'5 x' t'3 s'6 vs t'4
      s'7 prev t'5 s'8 x'' t'6.
     type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
     lift_option_type (get_module_code cx src_id_opt)
       "IntCall get_module_code" s'3 = (INL ts,t') ∧
     lift_option_type (lookup_callable_function cx.in_deploy fn ts)
       "IntCall lookup_function" s'4 = (INL tup,t'') ∧
     type_check
       (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
        LENGTH (FST (SND (SND tup))) ≤
        LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
       "IntCall args length" s'5 = (INL x',t'3) ∧
     eval_exprs cx es s'6 = (INL vs,t'4) ∧
     get_scopes s'7 = (INL prev,t'5) ∧
     set_scopes [FEMPTY] s'8 = (INL x'',t'6) ⇒
     ∀s exc st'.
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP
            (LENGTH (FST (SND (SND (SND tup)))) −
             (LENGTH (FST (SND (SND tup))) − LENGTH es))
            (FST (SND (SND (SND tup))))) s = (INR exc,st') ⇒
       no_control_exc exc) ∧
  (∀s'' x t s'3 ts t' s'4 tup t'' s'5 x' t'3.
     type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
     lift_option_type (get_module_code cx src_id_opt)
       "IntCall get_module_code" s'3 = (INL ts,t') ∧
     lift_option_type (lookup_callable_function cx.in_deploy fn ts)
       "IntCall lookup_function" s'4 = (INL tup,t'') ∧
     type_check
       (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
        LENGTH (FST (SND (SND tup))) ≤
        LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
       "IntCall args length" s'5 = (INL x',t'3) ⇒
     ∀s exc st'. eval_exprs cx es s = (INR exc,st') ⇒
       no_control_exc exc) ⇒
  ∀s exc st'.
    eval_expr cx (Call v16 (IntCall (src_id_opt,fn)) es v17) s =
    (INR exc,st') ⇒ no_control_exc exc
Proof
  rpt strip_tac >> pop_assum mp_tac
  >> PURE_REWRITE_TAC[Once evaluate_def] >> strip_tac
  >> step_tac >- close_type_check
  >> step_tac >- close_lift_option_type
  >> step_tac >- close_lift_option_type
  >> step_tac >- close_type_check
  >> step_tac >- (res_tac >> gvs[no_control_exc_def])
  >> step_tac >- gvs[get_scopes_def, return_def]
  >> step_tac >- (
    drule finally_no_control >>
    disch_then irule >>
    conj_tac >- simp at_mono >>
    rpt gen_tac >> strip_tac >>
    step_tac >- (gvs at_mono) >>
    metis_tac[])
  >> pop_assum mp_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM DE_MORGAN_THM]
  >> strip_tac >> drule int_call_tail_no_control >> simp[]
QED

Theorem eval_raw_call_no_control:
  eval_raw_call cx flags target_addr calldata amount st = (INR exc, st') ==>
  no_control_exc exc
Proof
  Cases_on `~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
    ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0)` >>
  fs[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def,
       get_transient_storage_def, no_control_exc_def] >>
  Cases_on `run_raw_call cx flags target_addr calldata amount
    st.accounts st.tStorage` >>
  simp[lift_option_def, bind_def, return_def, raise_def, no_control_exc_def] >>
  rename1 `run_raw_call _ _ _ _ _ _ _ = SOME call_result` >>
  PairCases_on `call_result` >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `call_result0` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[update_accounts_def, update_transient_def, append_logs_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def,
       no_control_exc_def] >>
  rpt strip_tac >> gvs[]
QED

(* ===== Case 20: RawCallTarget ===== *)

Theorem raw_call_no_control[local]:
  ∀cx ty flags es v18.
  (∀s exc st'. eval_exprs cx es s = (INR exc,st') ⇒ no_control_exc exc) ⇒
  ∀s exc st'.
    eval_expr cx (Call ty (RawCallTarget flags) es v18) s =
    (INR exc,st') ⇒ no_control_exc exc
Proof
  rpt strip_tac >> pop_assum mp_tac
  >> simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, lift_option_type_def, return_def, raise_def,
          option_CASE_rator, AllCaseEqs()]
  >> rpt strip_tac >> gvs[no_control_exc_def]
  >> imp_res_tac eval_raw_call_no_control >> res_tac >> gvs[no_control_exc_def]
QED

Theorem raw_call_calldata_no_control[local]:
  ∀cx ty flags es drv.
  (∀s exc st'. eval_exprs cx es s = (INR exc,st') ⇒ no_control_exc exc) ⇒
  ∀s exc st'.
    eval_expr cx (Call ty (RawCallCalldataTarget flags) es drv) s =
      (INR exc,st') ⇒ no_control_exc exc
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, return_def, raise_def,
       option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[no_control_exc_def] >>
  imp_res_tac eval_raw_call_no_control >> res_tac >> gvs[no_control_exc_def]
QED

(* ===== Main theorem ===== *)

val eval_expr_bt_ind = evaluate_ind
  |> Q.SPECL [`\cx s. T`, `\cx ss. T`, `\cx it. T`, `P_bt`,
              `\cx ty nm body vs. T`, `P_expr`, `P_exprs`,
              `\cx e. T`, `\cx t. T`, `\cx t. T`,
              `\cx g v. T`, `\cx gs vs. T`]
  |> SIMP_RULE std_ss [];

Theorem eval_expr_no_control_with_bt:
  (∀cx bt s exc st'.
    eval_base_target cx bt s = (INR exc, st') ⇒
    no_control_exc exc) ∧
  (∀cx e s exc st'.
    eval_expr cx e s = (INR exc, st') ⇒
    no_control_exc exc) ∧
  (∀cx es s exc st'.
    eval_exprs cx es s = (INR exc, st') ⇒
    no_control_exc exc)
Proof
  ho_match_mp_tac eval_expr_bt_ind >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- (
    rename1`SubscriptTarget` >>
    unfold_tac >>
    PairCases_on`x` >>
    gvs[bind_def, return_def, AllCaseEqs()] >>
    resolve_tac) >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- (
    rename1`Pop` >>
    unfold_tac >>
    PairCases_on`x` >>
    gvs[bind_def, return_def, AllCaseEqs()] >>
    resolve_tac) >>
  conj_tac >- unfold_tac >>
  conj_tac >- (
    rpt strip_tac >> pop_assum mp_tac >>
    simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
         assert_def, return_def, raise_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[no_control_exc_def] >>
    imp_res_tac eval_send_no_control >> gvs[no_control_exc_def] >>
    first_x_assum (qspecl_then [`s`, `s`] mp_tac) >>
    simp[type_check_def, assert_def, return_def] >>
    disch_then drule >> simp[]) >>
  conj_tac >- (
    rpt strip_tac >> pop_assum mp_tac >>
    simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >>
    imp_res_tac eval_ext_call_no_control >> res_tac) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    match_mp_tac int_call_no_control >>
    metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> drule_all raw_call_no_control >> simp[]) >>
  conj_tac >- (rpt strip_tac >> drule_all raw_call_calldata_no_control >> simp[]) >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- unfold_tac >>
  conj_tac >- suspend "CreateTarget" >>
  rpt conj_tac >> unfold_tac
QED

Resume eval_expr_no_control_with_bt[CreateTarget]:
  rpt gen_tac >> strip_tac >>
  Cases_on `kind` >> gvs[] >> unfold_tac
QED

Finalise eval_expr_no_control_with_bt

Theorem eval_expr_no_control:
  (∀cx e s exc st'.
    eval_expr cx e s = (INR exc, st') ⇒
    no_control_exc exc) ∧
  (∀cx es s exc st'.
    eval_exprs cx es s = (INR exc, st') ⇒
    no_control_exc exc)
Proof
  metis_tac[eval_expr_no_control_with_bt]
QED

(* Place operations expose exception boundaries independently of state frames. *)
Theorem read_place_no_control:
  read_place cx p st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `p` >> simp[read_place_def, bind_def, get_scopes_def,
    return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[read_storage_slot_no_control, get_immutables_no_control,
    lift_option_type_no_control, lift_sum_no_control]
QED

Theorem read_place_or_value_no_control:
  read_place_or_value cx pv st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> simp[read_place_or_value_def] >>
  metis_tac[read_place_no_control, materialise_no_control]
QED

Theorem place_type_value_no_control:
  place_type_value cx p st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `p` >> simp[place_type_value_def, bind_def, get_scopes_def,
    return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[get_immutables_no_control, lift_option_type_no_control]
QED

Theorem write_place_no_control:
  write_place cx p v st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `p` >> simp[write_place_def, bind_def, ignore_bind_def,
    get_scopes_def, set_scopes_def, return_def, prod_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, return_def, AllCaseEqs()] >>
  metis_tac[write_storage_slot_no_control, get_immutables_no_control,
    set_immutable_no_control, lift_option_type_no_control,
    type_check_no_control, lift_sum_no_control]
QED

Theorem extend_storage_place_no_control:
  extend_storage_place cx tr slot tv sb st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[extend_storage_place_def, bind_def, return_def, raise_def,
    no_control_exc_def, AllCaseEqs()] >>
  TRY (rename1 `ValueSubscript v` >> Cases_on `v` >>
    gvs[extend_storage_place_def, bind_def, return_def, raise_def,
      ignore_bind_def, check_def, assert_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator,
      no_control_exc_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[return_def]) >>
  metis_tac[lift_option_type_no_control, resolve_array_element_no_control,
    no_control_exc_def]
QED

Theorem extend_place_no_control:
  extend_place cx tv pv sb st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >>
  TRY (rename1 `PlaceR p` >> Cases_on `p`) >>
  TRY (rename1 `ValueR v` >> Cases_on `v`) >> Cases_on `sb` >>
  simp[extend_place_def, bind_def, ignore_bind_def, return_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[raise_def] >>
  TRY (simp[no_control_exc_def] >> NO_TAC) >>
  metis_tac[extend_storage_place_no_control, place_type_value_no_control,
    read_place_no_control, get_Value_no_control, lift_sum_no_control]
QED

Theorem extend_target_place_no_control:
  extend_target_place cx pv sb st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> TRY (rename1 `ValueR v` >> Cases_on `v`) >>
  simp[extend_target_place_def, raise_def, no_control_exc_def] >>
  metis_tac[extend_place_no_control, no_control_exc_def]
QED

Theorem get_place_no_control:
  get_place pv st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def, no_control_exc_def]
QED

Theorem lookup_global_place_no_control:
  lookup_global_place cx src id st = (INR exc,st') ==> no_control_exc exc
Proof
  simp[lookup_global_place_def, bind_def, return_def, raise_def,
    option_CASE_rator, prod_CASE_rator, var_decl_info_CASE_rator,
    AllCaseEqs()] >> rpt strip_tac >> gvs[AllCaseEqs(), bind_def,
    raise_def, return_def] >>
  TRY (simp[no_control_exc_def] >> NO_TAC) >>
  metis_tac[lift_option_type_no_control, get_immutables_no_control]
QED

Theorem eval_place_no_control:
  !e cx st exc st'. eval_place cx e st = (INR exc,st') ==> no_control_exc exc
Proof
  Induct_on `e` >> rpt gen_tac >>
  TRY (rename1 `TopLevelName ty root` >> PairCases_on `root`) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
    return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[eval_expr_no_control, type_check_no_control,
    lookup_global_place_no_control, get_Value_no_control,
    lift_option_type_no_control, extend_place_no_control]
QED

Theorem eval_base_place_no_control:
  !t cx st exc st'. eval_base_place cx t st = (INR exc,st') ==> no_control_exc exc
Proof
  Induct_on `t` >> rpt gen_tac >>
  TRY (rename1 `TopLevelNameTarget root` >> PairCases_on `root`) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def, return_def,
    AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[eval_expr_no_control, type_check_no_control,
    lookup_global_place_no_control, get_Value_no_control,
    extend_target_place_no_control]
QED

Theorem eval_target_place_no_control:
  eval_target_place cx t st = (INR exc,st') ==> no_control_exc exc
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[eval_base_place_no_control, get_place_no_control]
QED

val tuple_no_control_ind = evaluate_ind
  |> Q.SPECL [`\cx s. T`, `\cx ss. T`, `\cx it. T`, `\cx t. T`,
              `\cx ty nm body vs. T`, `\cx e. T`, `\cx es. T`,
              `\cx e. T`, `\cx t. T`, `\cx t. T`]
  |> SIMP_RULE std_ss [];

Theorem tuple_store_no_control[local]:
  (!cx g v st exc st'. assign_tuple_targets cx g v st = (INR exc,st') ==>
    no_control_exc exc) /\
  (!cx gs vs st exc st'. assign_tuple_target_list cx gs vs st = (INR exc,st') ==>
    no_control_exc exc)
Proof
  ho_match_mp_tac tuple_no_control_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> qpat_x_assum `_ = (INR exc,st')` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
    vyperValueTheory.value_CASE_rator, vyperValueTheory.array_value_CASE_rator,
    return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  TRY (simp[no_control_exc_def] >> NO_TAC) >>
  metis_tac[eval_target_place_no_control, write_place_no_control]
QED

Theorem assign_tuple_targets_no_control:
  assign_tuple_targets cx g v st = (INR exc,st') ==> no_control_exc exc
Proof
  metis_tac[tuple_store_no_control]
QED

(* Place/control integration audit. *)
val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("No-control oracle debt: " ^ name)
  end) (DB.thms "vyperExprNoControl");
