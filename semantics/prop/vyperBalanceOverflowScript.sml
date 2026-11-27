(* Total-balance preservation for oracle-mode source evaluation. *)
Theory vyperBalanceOverflow
Ancestors
  vyperInterpreter vyperState vyperEvalOutcomeSuffix vyperCallOutcome vyperCallOutcomeProps vyperCallFrame
  vyperCreateFrame vyperFiniteStoragePreservation vfmTotalBalance vfmState vfmTypes[qualified,ignore_grammar] extCallOracle[qualified,ignore_grammar] vyperStatePreservation[qualified,ignore_grammar] vyperStorageBackend vyperMisc vyperConstantsStorageFrame[qualified] vyperPureReadingErrors[qualified]
Libs monadsyntax pairLib evalWalkLib

val () = monadsyntax.enable_monad "vyper_evaluation";

Definition source_balance_bounded_def:
  source_balance_bounded B st <=>
    ?os. st.outcomes = SOME os /\
         total_balance st.accounts <= B /\
         EVERY (\co. total_balance co.co_accounts <= B) os
End

Definition source_result_ok_def:
  source_result_ok r <=>
    case r of
      INR (Error (RuntimeError msg)) => msg <> "transfer_value recipient overflow"
    | _ => T
End

Theorem source_balance_bounded_abstract_machine[local]:
  source_balance_bounded B st ==>
  total_balance (abstract_machine_from_state srcs exps layouts st).accounts <= B
Proof
  strip_tac >> fs[source_balance_bounded_def, abstract_machine_from_state_def]
QED

Theorem abstract_machine_balance_eq[local]:
  total_balance (abstract_machine_from_state srcs exps layouts st).accounts <= B /\
  abstract_machine_from_state srcs exps layouts st = am ==>
  total_balance am.accounts <= B
Proof
  strip_tac >> gvs[]
QED

Theorem machine_balance_eq[local]:
  total_balance am.accounts <= B /\ am = am_out ==>
  total_balance am_out.accounts <= B
Proof
  strip_tac >> gvs[]
QED

Theorem finalize_pending_deletions_balance_bounded[local]:
  total_balance am.accounts <= B ==>
  total_balance (finalize_pending_deletions am).accounts <= B
Proof
  strip_tac >> simp[finalize_pending_deletions_def] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `total_balance am.accounts` >> simp[] >>
  irule vfmTotalBalanceTheory.total_balance_process_deletions
QED

Theorem source_machine_sources_update_balance[local]:
  total_balance am.accounts <= B ==>
  total_balance (am with sources updated_by CONS (addr,mods)).accounts <= B
Proof
  strip_tac >> simp[]
QED

Theorem two_balances_le_total_balance:
  fromAddr <> toAddr ==>
  (lookup_account fromAddr accounts).balance +
    (lookup_account toAddr accounts).balance <= total_balance accounts
Proof
  strip_tac >>
  qspecl_then [`toAddr`, `update_account fromAddr empty_account_state accounts`]
    mp_tac (GEN_ALL lookup_balance_le_total_balance) >>
  qspecl_then [`fromAddr`, `empty_account_state`, `accounts`] mp_tac
    (GEN_ALL total_balance_update_account) >>
  simp[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM,
       empty_account_state_def] >> decide_tac
QED

Theorem source_transfer_value_no_recipient_overflow:
  source_balance_bounded (2 ** 256 - 1) st /\
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  source_result_ok res
Proof
  strip_tac >>
  `source_balance_bounded (2 ** 256 - 1) st /\
   transfer_value fromAddr toAddr amount st = (res,st')` by simp[] >>
  Cases_on `res` >> simp[source_result_ok_def] >>
  drule concrete_send_error >> strip_tac >> gvs[] >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def,
     check_def, assert_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  fs[source_balance_bounded_def] >>
  Cases_on `amount ≤ (lookup_account fromAddr st.accounts).balance` >>
  simp[] >>
  qspecl_then [`fromAddr`, `toAddr`, `st.accounts`] mp_tac
    (GEN_ALL two_balances_le_total_balance) >>
  impl_tac >- simp[] >>
  decide_tac
QED

Theorem source_transfer_value_preserves_bound:
  source_balance_bounded B st /\
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  source_balance_bounded B st'
Proof
  strip_tac >> fs[source_balance_bounded_def] >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def,
     check_def, assert_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), source_balance_bounded_def] >>
  Cases_on `amount <= (lookup_account fromAddr st.accounts).balance` >>
  simp[] >>
  qmatch_goalsub_abbrev_tac
    `total_balance (update_account fromAddr d (update_account toAddr r st.accounts)) ≤ B` >>
  `lookup_account fromAddr (update_account toAddr r st.accounts) =
     lookup_account fromAddr st.accounts` by
    simp[lookup_account_def, update_account_def,
         combinTheory.APPLY_UPDATE_THM] >>
  `update_account fromAddr d (update_account toAddr r st.accounts) =
     vfmExecution$transfer_value fromAddr toAddr amount st.accounts` by
    simp[vfmExecutionTheory.transfer_value_def, Abbr`d`, Abbr`r`,
         lookup_account_def, update_account_def,
         combinTheory.APPLY_UPDATE_THM, combinTheory.UPDATE_COMMUTES] >>
  qpat_x_assum
    `update_account fromAddr d (update_account toAddr r st.accounts) =
       vfmExecution$transfer_value fromAddr toAddr amount st.accounts`
    (fn h => once_rewrite_tac[h]) >>
  `total_balance (vfmExecution$transfer_value fromAddr toAddr amount st.accounts) =
     total_balance st.accounts` by
    (irule vfmTotalBalanceTheory.total_balance_transfer_value >>
     first_assum ACCEPT_TAC) >>
  rw[]
QED

(* Local bookkeeping and control flow do not change the account total or
   the outcome stream. Exception handlers may rethrow their input. *)
Theorem source_balance_ordinary_primitives:
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     get_scopes st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     set_scopes env st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     push_scope st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     pop_scope st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     push_scope_with_var nm tv v st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     new_variable nm tv v st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     push_function src_fn sc cx st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     pop_function env st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     get_accounts st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     get_transient_storage st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     update_transient ft st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     update_pending_deletions fp st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     push_log lg st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     append_logs ls st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     record_storage_event obs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     record_storage_backend st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     next_gas_reading st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     check_not_static cx st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     frame_call_value cx vo st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     acquire_nonreentrant_lock addr slot view st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     release_nonreentrant_lock addr slot st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     lock_if_nr cx nr view st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     unlock_if_nr cx nr view st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     source_result_ok (INR e) /\ handle_loop_exception e st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st res st'. source_balance_bounded (2 ** 256 - 1) st /\
     source_result_ok (INR e) /\ handle_function e st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!st. source_balance_bounded (2 ** 256 - 1) st ==> IS_SOME st.outcomes)
Proof
  rpt conj_tac >>
  simp[get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
       push_scope_with_var_def, new_variable_def, push_function_def, pop_function_def,
       get_accounts_def, get_transient_storage_def, update_transient_def,
       update_pending_deletions_def, push_log_def, append_logs_def,
       record_storage_event_def, record_storage_backend_def, next_gas_reading_def,
       frame_call_value_def, acquire_nonreentrant_lock_def,
       release_nonreentrant_lock_def, lock_if_nr_def, unlock_if_nr_def,
       check_not_static_eq, type_check_def, check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def,
       COND_RATOR, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.list_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[source_balance_bounded_def, source_result_ok_def] >>
  Cases_on `e` >> gvs[handle_loop_exception_def, handle_function_def,
                      return_def, raise_def, source_result_ok_def]
QED

Theorem source_adopt_call_outcome_preserves_bound:
  source_balance_bounded B st /\
  total_balance outcome.co_accounts <= B /\
  adopt_call_outcome rq outcome st = (res,st') ==>
  source_balance_bounded B st'
Proof
  strip_tac >> fs[source_balance_bounded_def] >>
  qpat_x_assum `adopt_call_outcome _ _ _ = _` mp_tac >>
  rw[adopt_call_outcome_equation] >>
  Cases_on `rq.cr_static` >> gvs[] >>
  Cases_on `outcome.co_success` >> gvs[] >>
  Cases_on `rq.cr_kind = MessageCall` >> gvs[]
QED

Theorem source_balance_walk_bind:
  source_balance_bounded B st /\
  (!r mid. source_balance_bounded B st /\ f st = (r,mid) ==>
    source_balance_bounded B mid /\ source_result_ok r) /\
  (!v mid r t. f st = (INL v,mid) /\ source_balance_bounded B mid /\
    g v mid = (r,t) ==>
    source_balance_bounded B t /\ source_result_ok r) /\
  monad_bind f g st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> gvs[bind_def, source_result_ok_def] >>
  metis_tac[]
QED

Theorem source_balance_walk_finally:
  source_balance_bounded B st /\
  (!r mid. source_balance_bounded B st /\ f st = (r,mid) ==>
    source_balance_bounded B mid /\ source_result_ok r) /\
  (!v mid r t. f st = (v,mid) /\ source_balance_bounded B mid /\
    g mid = (r,t) ==>
    source_balance_bounded B t /\ source_result_ok r) /\
  finally f g st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> Cases_on `g r` >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def,
      source_result_ok_def] >>
  Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem source_balance_walk_finally_unless_halt:
  source_balance_bounded B st /\
  (!r mid. source_balance_bounded B st /\ f st = (r,mid) ==>
    source_balance_bounded B mid /\ source_result_ok r) /\
  (!v mid r t. f st = (v,mid) /\ source_balance_bounded B mid /\
    g mid = (r,t) ==>
    source_balance_bounded B t /\ source_result_ok r) /\
  finally_unless_halt f g st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  rpt strip_tac >>
  Cases_on `f st` >> Cases_on `q` >> Cases_on `g r` >>
  gvs[finally_unless_halt_def, ignore_bind_def, bind_def,
      return_def, raise_def, source_result_ok_def] >>
  Cases_on `q` >> gvs[] >> BasicProvers.every_case_tac >>
  gvs[] >> metis_tac[]
QED

Theorem source_balance_walk_lifts:
  (!x st res st'.
    source_balance_bounded B st /\ lift_sum x st = (res,st') /\
    x <> INR (RuntimeError "transfer_value recipient overflow") ==>
    source_balance_bounded B st' /\ source_result_ok res) /\
  (!x st res st'.
    source_balance_bounded B st /\ lift_sum_runtime x st = (res,st') /\
    x <> INR "transfer_value recipient overflow" ==>
    source_balance_bounded B st' /\ source_result_ok res) /\
  (!x msg st res st'.
    source_balance_bounded B st /\ lift_option x msg st = (res,st') /\
    msg <> "transfer_value recipient overflow" ==>
    source_balance_bounded B st' /\ source_result_ok res) /\
  (!x msg st res st'.
    source_balance_bounded B st /\ lift_option_type x msg st = (res,st') /\
    msg <> "transfer_value recipient overflow" ==>
    source_balance_bounded B st' /\ source_result_ok res) /\
  (!b msg st res st'.
    source_balance_bounded B st /\ check b msg st = (res,st') /\
    msg <> "transfer_value recipient overflow" ==>
    source_balance_bounded B st' /\ source_result_ok res) /\
  (!b msg st res st'.
    source_balance_bounded B st /\ type_check b msg st = (res,st') /\
    msg <> "transfer_value recipient overflow" ==>
    source_balance_bounded B st' /\ source_result_ok res)
Proof
  rpt conj_tac
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `x` >>
      gvs[lift_sum_def, return_def, raise_def, source_result_ok_def] >>
      Cases_on `y` >> gvs[] >> metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `x` >>
      gvs[lift_sum_runtime_def, return_def, raise_def, source_result_ok_def] >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `x` >>
      gvs[lift_option_def, return_def, raise_def, source_result_ok_def] >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >>
      Cases_on `x` >>
      gvs[lift_option_type_def, return_def, raise_def, source_result_ok_def] >>
      metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >> Cases_on `b` >>
      gvs[check_def, type_check_def, assert_def, return_def, raise_def,
          source_result_ok_def] >> metis_tac[])
  >- (rpt gen_tac >> rpt strip_tac >> Cases_on `b` >>
      gvs[type_check_def, assert_def, return_def, raise_def,
          source_result_ok_def] >> metis_tac[])
QED

(* Balance preservation for storage and place operations. *)
Theorem source_balance_set_storage:
  source_balance_bounded B st ==> source_balance_bounded B (set_storage cx st tr ss)
Proof
  Cases_on `tr` >>
  simp[source_balance_bounded_def, set_storage_def, GSYM update_account_def] >>
  qmatch_goalsub_abbrev_tac
    `total_balance (update_account a (st.accounts a with storage := ss) st.accounts)` >>
  `total_balance (update_account a (st.accounts a with storage := ss) st.accounts) =
     total_balance st.accounts` suffices_by simp[] >>
  irule total_balance_update_account_same >> simp[lookup_account_def]
QED

val balance_place_safe = ``\f. !st res st'.
  source_balance_bounded (2 ** 256 - 1) st /\ f st = (res,st') ==>
  source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res``;
fun balance_place_as ty = inst [alpha |-> ty] balance_place_safe;
val balance_place_unit = balance_place_as ``:unit``;
val balance_place_overflow = ``"transfer_value recipient overflow"``;

Theorem balance_place_ok[local]:
  source_result_ok r <=> r <> INR (Error (RuntimeError ^balance_place_overflow))
Proof
  Cases_on `r` >> simp[source_result_ok_def] >>
  Cases_on `y` >> simp[source_result_ok_def] >>
  Cases_on `e` >> simp[source_result_ok_def]
QED

Theorem balance_place_bind[local]:
  (^balance_place_safe f /\ (!v. ^(balance_place_as ``:β``) (g v))) ==>
  ^(balance_place_as ``:β``) (monad_bind f g)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> disch_then strip_assume_tac >>
  namedCases_on `f st` ["r mid"] >>
  `source_balance_bounded (2 ** 256 - 1) mid /\ source_result_ok r` by
    (qpat_assum `!s v t. _ /\ f s = (v,t) ==> _`
      (qspecl_then [`st`,`r`,`mid`] mp_tac) >> simp[]) >>
  Cases_on `r` >> gvs[bind_def]
  >- (qpat_assum `!v s r t. _ /\ g v s = (r,t) ==> _`
        (qspecl_then [`x`,`mid`,`res`,`st'`] mp_tac) >> simp[]) >>
  gvs[balance_place_ok]
QED

Theorem balance_place_leaves[local]:
  ^balance_place_safe (return v) /\
  (e <> Error (RuntimeError ^balance_place_overflow) ==> ^balance_place_safe (raise e)) /\
  (x <> INR (RuntimeError ^balance_place_overflow) ==> ^balance_place_safe (lift_sum x)) /\
  ^balance_place_safe (lift_option_type opt msg) /\
  (msg <> ^balance_place_overflow ==> ^balance_place_unit (check b msg)) /\
  ^balance_place_unit (type_check b msg)
Proof
  Cases_on `x` >> Cases_on `opt` >> Cases_on `b` >>
  simp[return_def, raise_def, lift_sum_def, lift_option_type_def, check_def,
       type_check_def, assert_def, balance_place_ok]
QED

Theorem balance_place_storage_ops[local]:
  ^(balance_place_as ``:storage``) (get_storage_backend cx tr) /\
  ^(balance_place_as ``:value``) (read_storage_slot cx tr slot tv) /\
  ^balance_place_unit (write_storage_slot cx tr slot tv v)
Proof
  BETA_TAC >> simp[get_storage_backend_eq, read_storage_slot_eq, write_storage_slot_eq] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[balance_place_ok] >>
  irule source_balance_set_storage >> first_assum ACCEPT_TAC
QED

Theorem balance_place_local_ops[local]:
  ^(balance_place_as ``:scope list``) get_scopes /\
  ^balance_place_unit (set_scopes scs) /\
  ^(balance_place_as ``:string |-> (type_value # value)``) (get_immutables cx src) /\
  ^balance_place_unit (set_immutable cx src id tv v) /\
  ^balance_place_unit (record_storage_event obs)
Proof
  simp[get_scopes_def, set_scopes_def, get_immutables_def,
       get_address_immutables_def, set_immutable_def, set_address_immutables_def,
       record_storage_event_def, bind_def, lift_option_type_def,
       return_def, raise_def, source_balance_bounded_def, balance_place_ok,
       option_CASE_rator, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

(* Match monadic heads before inspecting cases in their data arguments. *)

fun BALANCE_PLACE_WALK facts unfolds =
  let
    val normalise = CONV_RULE (DEPTH_CONV BETA_CONV)
    val leaves = List.concat (map (CONJUNCTS o SPEC_ALL o normalise)
      (balance_place_leaves :: balance_place_storage_ops :: balance_place_local_ops :: facts))
    val accept = FIRST (map (fn th => MATCH_ACCEPT_TAC th ORELSE
      (MATCH_MP_TAC th >> (simp[] >> NO_TAC))) leaves)
    val unfold = evalWalkLib.unfold_conv (ignore_bind_def :: unfolds)
    val at = STRIP_QUANT_CONV o LAND_CONV o RAND_CONV o LHS_CONV o RATOR_CONV
  in
    BETA_TAC >> rpt (FIRST [first_assum MATCH_ACCEPT_TAC, accept,
      MATCH_MP_TAC (normalise balance_place_bind) >> conj_tac,
      CONV_TAC (at unfold), CONV_TAC (at (CHANGED_CONV evalWalkLib.head_conv)),
      CONV_TAC (HO_REWR_CONV pairTheory.FORALL_PROD), gen_tac,
      evalWalkLib.HEAD_CASE_TAC])
  end;

Theorem balance_place_resolve[local]:
  !path cx tr slot tv. ^(balance_place_as ``:bytes32 # type_value # subscript list``)
    (resolve_array_element cx tr slot tv path)
Proof
  BETA_TAC >> Induct >>
  simp_tac bool_ss [Once (oneline resolve_array_element_def)] >>
  BALANCE_PLACE_WALK [] []
QED

Theorem balance_place_basic[local]:
  ^(balance_place_as ``:type_value``) (place_type_value cx p) /\
  ^(balance_place_as ``:place``) (get_place pv) /\
  ^(balance_place_as ``:place``) (extend_storage_place cx tr slot tv sb)
Proof
  conj_tac >- (Cases_on `p` >> BALANCE_PLACE_WALK [] [place_type_value_def]) >>
  conj_tac >- (Cases_on `pv` >> BALANCE_PLACE_WALK [] [get_place_def]) >>
  BALANCE_PLACE_WALK [balance_place_resolve] [oneline extend_storage_place_def]
QED

val balance_place_exclusions = ``
  (!tv v path. evaluate_subscripts tv v path <> INR (RuntimeError ^balance_place_overflow)) /\
  (!entry path. read_memory_path entry path <> INR (RuntimeError ^balance_place_overflow)) /\
  (!tv a path ao. assign_subscripts tv a path ao <> INR (RuntimeError ^balance_place_overflow)) /\
  (!entry path v. replace_memory_entry entry path v <> INR (RuntimeError ^balance_place_overflow)) /\
  (!tv a v. append_element tv a v <> INR (RuntimeError ^balance_place_overflow)) /\
  (!a. pop_element a <> INR (RuntimeError ^balance_place_overflow)) /\
  (!a. popped_value a <> INR (RuntimeError ^balance_place_overflow))``;

Theorem balance_place_io[local]:
  ^balance_place_exclusions ==>
  (!cx p. ^(balance_place_as ``:value``) (read_place cx p)) /\
  (!cx p v. ^balance_place_unit (write_place cx p v)) /\
  (!cx src n. ^(balance_place_as ``:eval_result``) (lookup_global cx src n)) /\
  (!cx nsid mid. ^(balance_place_as ``:eval_result``) (lookup_flag_mem cx nsid mid))
Proof
  strip_tac >> rpt conj_tac
  >- (map_every qx_gen_tac [`cx`, `p`] >> Cases_on `p` >>
      BALANCE_PLACE_WALK [] [read_place_def])
  >- (map_every qx_gen_tac [`cx`, `p`, `v`] >> Cases_on `p` >>
      BALANCE_PLACE_WALK [] [write_place_def])
  >- BALANCE_PLACE_WALK [] [lookup_global_def] >>
  BALANCE_PLACE_WALK [] [oneline lookup_flag_mem_def]
QED

Theorem balance_place_results[local]:
  ^balance_place_exclusions ==>
  (!cx pv. ^(balance_place_as ``:value``) (read_result cx pv)) /\
  (!cx pv sb. ^(balance_place_as ``:eval_result``) (extend_place cx pv sb)) /\
  (!cx pv. ^(balance_place_as ``:eval_result``) (conditional_result cx pv))
Proof
  strip_tac >> mp_tac balance_place_io >> impl_tac >- simp[] >>
  BETA_TAC >> strip_tac >> rpt conj_tac
  >- (map_every qx_gen_tac [`cx`,`pv`] >> Cases_on `pv` >>
      BALANCE_PLACE_WALK [] [read_result_def])
  >- BALANCE_PLACE_WALK [balance_place_basic] [oneline extend_place_def] >>
  map_every qx_gen_tac [`cx`,`pv`] >> Cases_on `pv` >>
  BALANCE_PLACE_WALK [balance_place_basic] [conditional_result_def]
QED

Theorem balance_place_array_length[local]:
  ^balance_place_exclusions ==>
  (!cx pv. ^(balance_place_as ``:num``) (result_array_length cx pv))
Proof
  strip_tac >> mp_tac balance_place_results >> impl_tac >- simp[] >>
  BETA_TAC >> strip_tac >> BALANCE_PLACE_WALK [] [oneline result_array_length_def]
QED

(* The memory-pop update propagates only the two checked subscript errors. *)

Theorem balance_place_pop_update[local]:
  ^balance_place_exclusions ==>
  !entry path shortened.
    (case evaluate_subscripts entry.type entry.value path of
     | INL _ =>
         (case assign_subscripts entry.type entry.value path (Replace shortened) of
          | INL updated => INL (updated,entry.popped)
          | INR err => INR err)
     | INR err =>
         (case replace_popped entry.type path shortened entry.popped of
          | SOME history => INL (entry.value,history)
          | NONE => INR err)) <> INR (RuntimeError ^balance_place_overflow)
Proof
  strip_tac >> simp[AllCaseEqs()]
QED

Theorem source_balance_place_primitives:
  ^balance_place_exclusions ==>
  (!cx p. ^(balance_place_as ``:value``) (read_place cx p)) /\
  (!cx p v. ^balance_place_unit (write_place cx p v)) /\
  (!cx src n. ^(balance_place_as ``:eval_result``) (lookup_global cx src n)) /\
  (!cx nsid mid. ^(balance_place_as ``:eval_result``) (lookup_flag_mem cx nsid mid)) /\
  (!cx pv. ^(balance_place_as ``:value``) (read_result cx pv)) /\
  (!cx pv sb. ^(balance_place_as ``:eval_result``) (extend_place cx pv sb)) /\
  (!cx pv. ^(balance_place_as ``:eval_result``) (conditional_result cx pv)) /\
  (!cx pv. ^(balance_place_as ``:num``) (result_array_length cx pv)) /\
  (!cx p. ^(balance_place_as ``:type_value``) (place_type_value cx p)) /\
  (!pv. ^(balance_place_as ``:place``) (get_place pv)) /\
  (!cx ty pv sb. ^(balance_place_as ``:eval_result``) (select_result cx ty pv sb)) /\
  (!cx ty pv. ^(balance_place_as ``:eval_result list``) (array_iterator_results cx ty pv)) /\
  (!cx p v. ^balance_place_unit (append_place cx p v)) /\
  (!cx p. ^(balance_place_as ``:eval_result``) (pop_place cx p))
Proof
  strip_tac >>
  mp_tac balance_place_io >> impl_tac >- simp[] >> BETA_TAC >> strip_tac >>
  mp_tac balance_place_results >> impl_tac >- simp[] >> BETA_TAC >> strip_tac >>
  mp_tac balance_place_array_length >> impl_tac >- simp[] >> BETA_TAC >> strip_tac >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC)
  >- BALANCE_PLACE_WALK [balance_place_basic] []
  >- BALANCE_PLACE_WALK [balance_place_basic] []
  >- BALANCE_PLACE_WALK [] [oneline select_result_def]
  >- BALANCE_PLACE_WALK [] [array_iterator_results_def]
  >- BALANCE_PLACE_WALK [balance_place_basic] [oneline append_place_def] >>
  mp_tac balance_place_pop_update >> (impl_tac >- simp[]) >> strip_tac >>
  map_every qx_gen_tac [`cx`,`p`] >> Cases_on `p`
  >- BALANCE_PLACE_WALK [] [oneline pop_place_def]
  >- BALANCE_PLACE_WALK [] [pop_place_def] >>
  BALANCE_PLACE_WALK [] [pop_place_def]
QED

(* Selfdestruct's post-transfer update can only lower the total. *)
Theorem source_balance_zero_account:
  !a st res st'.
    source_balance_bounded (2 ** 256 - 1) st /\
    update_accounts (\acc. update_account a
      (lookup_account a acc with balance := 0) acc) st = (res,st') ==>
    source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res
Proof
  simp[update_accounts_def, return_def, source_result_ok_def] >>
  rpt strip_tac >> gvs[source_balance_bounded_def] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `total_balance st.accounts` >> simp[] >>
  irule total_balance_update_account_le >> simp[]
QED

(* Oracle call boundaries: both the residual stream and the selected
   outcome's account snapshot must be bounded before adoption. *)
Theorem take_call_boundary_local[local]:
  !gas_cap target calldata value_opt st res st'.
    source_balance_bounded (2 ** 256 - 1) st /\
    take_call_outcome gas_cap target calldata value_opt st = (res,st') ==>
    source_balance_bounded (2 ** 256 - 1) st' /\
    source_result_ok res /\
    (!rq outcome. res = INL (rq,outcome) ==>
       total_balance outcome.co_accounts <= 2 ** 256 - 1)
Proof
  rpt gen_tac >> strip_tac >>
  fs[source_balance_bounded_def] >>
  `outcomes_suffix (take_call_outcome gas_cap target calldata value_opt)` by
    MATCH_ACCEPT_TAC outcomes_suffix_take >>
  `outcome_suffix st.outcomes st'.outcomes` by
    (drule_all outcomes_suffix_result >> (simp[outcomes_suffix_result])) >>
  `!rest. st'.outcomes = SOME rest ==>
      EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) rest` by
    (`!x. st.outcomes = SOME x ==>
        EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) x` by
       (rpt gen_tac >> strip_tac >> gvs[]) >>
     metis_tac[outcome_suffix_EVERY]) >>
  `st'.accounts = st.accounts` by
    (metis_tac [take_call_outcome_preserved_fields, pairTheory.SND]) >>
  conj_tac
  >- (Cases_on `st'.outcomes` >> gvs[outcome_suffix_def])
  >- (conj_tac
      >- (Cases_on `res` >> simp[source_result_ok_def] >>
          rename1 `INR exc` >> drule take_call_outcome_error >> strip_tac >>
          gvs[source_result_ok_def])
      >> Cases_on `res` >> simp[] >>
         PairCases_on `x` >> rpt strip_tac >>
         drule take_call_outcome_success >> strip_tac >>
         gvs[] >> Cases_on `os` >>
         Cases_on `computed_precompile (call_outcome_request target calldata value_opt st with cr_gas := NONE)` >>
         gvs[extCallOracleTheory.take_outcome_def, call_outcome_request_def,
             extCallOracleTheory.computed_precompile_def] >>
         Cases_on `precompile_result target calldata` >>
         gvs[AllCaseEqs()])
QED

Theorem delegate_boundary_local[local]:
  !gas_cap target calldata value_opt st res st'.
    source_balance_bounded (2 ** 256 - 1) st /\
    take_delegate_outcome gas_cap target calldata value_opt st = (res,st') ==>
    source_balance_bounded (2 ** 256 - 1) st' /\
    source_result_ok res /\
    (!rq outcome. res = INL (rq,outcome) ==>
       total_balance outcome.co_accounts <= 2 ** 256 - 1)
Proof
  rpt gen_tac >> strip_tac >>
  fs[source_balance_bounded_def] >>
  `outcomes_suffix (take_delegate_outcome gas_cap target calldata value_opt)` by
    MATCH_ACCEPT_TAC outcomes_suffix_take_delegate >>
  `outcome_suffix st.outcomes st'.outcomes` by
    (drule_all outcomes_suffix_result >> (simp[outcomes_suffix_result])) >>
  `!rest. st'.outcomes = SOME rest ==>
      EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) rest` by
    (`!x. st.outcomes = SOME x ==>
        EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) x` by
       (rpt gen_tac >> strip_tac >> gvs[]) >>
     metis_tac[outcome_suffix_EVERY]) >>
  `st' = st with <|outcomes := st'.outcomes; requests := st'.requests;
                   storage_trace := st'.storage_trace|>` by
    (MATCH_MP_TAC take_delegate_outcome_frame >> first_assum ACCEPT_TAC) >>
  `st'.accounts = st.accounts` by
    gvs[evaluation_state_component_equality] >>
  conj_tac
  >- (Cases_on `st'.outcomes` >> gvs[outcome_suffix_def])
  >- (conj_tac
      >- (Cases_on `res` >> simp[source_result_ok_def] >>
          rename1 `INR exc` >> drule take_delegate_outcome_error >> strip_tac >>
          gvs[source_result_ok_def])
      >> Cases_on `res` >> simp[] >>
         PairCases_on `x` >> rpt strip_tac >>
         drule take_delegate_outcome_success >> strip_tac >>
         gvs[] >> Cases_on `os` >>
         Cases_on `computed_precompile (delegate_outcome_request target calldata value_opt st with cr_gas := NONE)` >>
         gvs[extCallOracleTheory.take_outcome_def, delegate_outcome_request_def,
             call_outcome_request_def, extCallOracleTheory.computed_precompile_def] >>
         Cases_on `precompile_result target calldata` >>
         gvs[AllCaseEqs()])
QED

Theorem source_balance_take_call_delegate:
  (!gas_cap target calldata value_opt st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     take_call_outcome gas_cap target calldata value_opt st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\
     source_result_ok res /\
     (!rq outcome. res = INL (rq,outcome) ==>
        total_balance outcome.co_accounts <= 2 ** 256 - 1)) /\
  (!gas_cap target calldata value_opt st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     take_delegate_outcome gas_cap target calldata value_opt st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\
     source_result_ok res /\
     (!rq outcome. res = INL (rq,outcome) ==>
        total_balance outcome.co_accounts <= 2 ** 256 - 1))
Proof
  conj_tac >> metis_tac[take_call_boundary_local, delegate_boundary_local]
QED

Theorem call_frame_error_ok_local[local]:
  frame_call_value cx v st = (INR e,st') ==> source_result_ok (INR e)
Proof
  rw[frame_call_value_def, ignore_bind_def, bind_def, check_def, assert_def,
     return_def, raise_def] >> gvs[AllCaseEqs(), raise_def, source_result_ok_def]
QED

Theorem ext_call_effects_boundary_local[local]:
  !cx target_addr calldata value_opt gas_opt accounts st res st'.
    source_balance_bounded (2 ** 256 - 1) st /\
    eval_ext_call_effects cx target_addr calldata value_opt gas_opt accounts st = (res,st') ==>
    source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `st.outcomes` >- gvs[source_balance_bounded_def] >>
  gvs[eval_ext_call_effects_def, bind_def, ignore_bind_def,
      return_def, raise_def, COND_RATOR, vfmTypesTheory.sum_CASE_rator,
      AllCaseEqs(), source_result_ok_def] >>
  drule_all (SIMP_RULE (srw_ss()) [] take_call_boundary_local) >> strip_tac >>
  gvs[source_result_ok_def] >>
  rename1 `take_call_outcome _ _ _ _ _ = (INL payload,_)` >>
  PairCases_on `payload` >>
  gvs[bind_def, return_def, raise_def, COND_RATOR, vfmTypesTheory.sum_CASE_rator,
      AllCaseEqs(), source_result_ok_def] >>
  imp_res_tac source_adopt_call_outcome_preserves_bound >>
  gvs[adopt_call_outcome_equation, source_result_ok_def]
QED

Theorem source_balance_oracle_call_primitives:
  (!bt vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     precompile_call_success bt vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx has_gas vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_send cx has_gas vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx flags target_addr calldata amount gas st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_raw_call cx flags target_addr calldata amount gas st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx target_addr calldata value_opt gas_opt accounts st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_ext_call_effects cx target_addr calldata value_opt gas_opt accounts st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx is_static skip_check sig opts vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     (!tenv ret_type returnData.
       evaluate_abi_decode_return tenv ret_type returnData <>
         INR "transfer_value recipient overflow") /\
     eval_ext_call cx is_static skip_check sig opts vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res)
Proof
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `st.outcomes` >- gvs[source_balance_bounded_def] >>
      qpat_x_assum `precompile_call_success _ _ _ = _` mp_tac >>
      rename1 `st.outcomes = SOME os` >> Cases_on `os` >>
      simp[precompile_call_success_def, bind_def, check_def, assert_def,
           return_def, raise_def, COND_RATOR, vfmTypesTheory.sum_CASE_rator,
           pairTheory.UNCURRY_RATOR, AllCaseEqs()] >>
      strip_tac >> gvs[source_result_ok_def] >>
      drule_all (SIMP_RULE (srw_ss()) [] take_call_boundary_local) >> strip_tac >>
      gvs[pairTheory.UNCURRY_EQ, combinTheory.C_THM, combinTheory.o_THM,
          AllCaseEqs(), assert_def, return_def, raise_def, source_result_ok_def])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `st.outcomes` >- gvs[source_balance_bounded_def] >>
      Cases_on `vs` >- gvs[eval_send_def, raise_def, source_result_ok_def] >>
      rename1 `eval_send _ _ (_::rest) _ = _` >> Cases_on `rest`
      >- gvs[eval_send_def, raise_def, source_result_ok_def] >>
      gvs[eval_send_def, frame_call_value_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, check_def, lift_option_type_def,
          return_def, raise_def, COND_RATOR, vfmTypesTheory.option_CASE_rator,
          vfmTypesTheory.sum_CASE_rator, AllCaseEqs(), source_result_ok_def] >>
      drule_all (SIMP_RULE (srw_ss()) [] take_call_boundary_local) >> strip_tac >>
      gvs[source_result_ok_def] >>
      rename1 `take_call_outcome _ _ _ _ _ = (INL payload,_)` >>
      PairCases_on `payload` >>
      gvs[bind_def, return_def, raise_def, assert_def, AllCaseEqs(),
          COND_RATOR, vfmTypesTheory.sum_CASE_rator, source_result_ok_def] >>
      imp_res_tac source_adopt_call_outcome_preserves_bound >>
      gvs[adopt_call_outcome_equation, source_result_ok_def])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `st.outcomes` >- gvs[source_balance_bounded_def] >>
      Cases_on `flags.rcf_is_delegate` >>
      gvs[eval_raw_call_def, frame_call_value_def, bind_def, ignore_bind_def,
          type_check_def, check_def, assert_def, return_def, raise_def,
          COND_RATOR, vfmTypesTheory.sum_CASE_rator, AllCaseEqs(),
          source_result_ok_def] >>
      FIRST [drule_all (SIMP_RULE (srw_ss()) [] take_call_boundary_local),
             drule_all (SIMP_RULE (srw_ss()) [] delegate_boundary_local)] >>
      strip_tac >> gvs[source_result_ok_def] >>
      FIRST [rename1 `take_call_outcome _ _ _ _ _ = (INL payload,_)`,
             rename1 `take_delegate_outcome _ _ _ _ _ = (INL payload,_)`] >>
      PairCases_on `payload` >>
      gvs[bind_def, return_def, raise_def, AllCaseEqs(), COND_RATOR,
          vfmTypesTheory.sum_CASE_rator, source_result_ok_def] >>
      imp_res_tac source_adopt_call_outcome_preserves_bound >>
      gvs[adopt_call_outcome_equation, source_result_ok_def])
  >- MATCH_ACCEPT_TAC ext_call_effects_boundary_local
  >- (rpt gen_tac >> strip_tac >> PairCases_on `sig` >>
      Cases_on `vs` >- gvs[eval_ext_call_def, raise_def, source_result_ok_def] >>
      gvs[eval_ext_call_def, bind_def, ignore_bind_def, type_check_def, check_def,
          assert_def, lift_option_type_def, return_def, raise_def, get_accounts_def] >>
      Cases_on `LENGTH t = LENGTH opts + LENGTH sig1 /\ ext_call_opts_ok is_static' opts` >>
      gvs[source_result_ok_def] >>
      Cases_on `dest_AddressV h` >>
      gvs[return_def, raise_def, source_result_ok_def] >>
      Cases_on `is_static'` >>
      gvs[bind_def, return_def, raise_def, vfmTypesTheory.option_CASE_rator,
          vfmTypesTheory.sum_CASE_rator, COND_RATOR] >>
      TRY (qmatch_asmsub_rename_tac
             `option_CASE (ext_call_kwarg EKValue opts kw_vals) _ _` >>
           Cases_on `ext_call_kwarg EKValue opts kw_vals` >>
           gvs[return_def, raise_def, vfmTypesTheory.option_CASE_rator] >>
           TRY (qmatch_asmsub_rename_tac `option_CASE (dest_NumV v) _ _` >>
                Cases_on `dest_NumV v` >> gvs[source_result_ok_def])) >>
      Cases_on `build_ext_calldata (get_tenv cx) sig0 sig1 (TAKE (LENGTH sig1) t)` >>
      gvs[source_result_ok_def] >>
      rename1 `dest_AddressV h = SOME target` >>
      Cases_on `ext_call_precheck_ok skip_check sig2 target st.accounts` >>
      gvs[source_result_ok_def] >>
      qmatch_asmsub_abbrev_tac `frame_call_value cx vreq st` >>
      Cases_on `frame_call_value cx vreq st` >>
      rename1 `frame_call_value _ _ _ = (fcv,_)` >>
      drule frame_call_value_state >> disch_then SUBST_ALL_TAC >>
      Cases_on `fcv` >> gvs[] >>
      imp_res_tac call_frame_error_ok_local >> gvs[source_result_ok_def] >>
      rename1 `frame_call_value _ _ _ = (INL value_opt,_)` >>
      qmatch_asmsub_abbrev_tac
        `eval_ext_call_effects cx target calldata value_opt gas st.accounts st` >>
      Cases_on `eval_ext_call_effects cx target calldata value_opt gas st.accounts st` >>
      rename1 `eval_ext_call_effects _ _ _ _ _ _ _ = (call_res,call_st)` >>
      drule_all (SIMP_RULE (srw_ss()) [] ext_call_effects_boundary_local) >>
      strip_tac >> Cases_on `call_res` >> gvs[source_result_ok_def] >>
      rename1 `eval_ext_call_effects _ _ _ _ _ _ _ = (INL return_data,_)` >>
      Cases_on `if return_data = [] then ext_call_kwarg EKDefault opts (DROP (LENGTH sig1) t) else NONE` >>
      gvs[lift_sum_runtime_def, get_accounts_def, assert_def, return_def, raise_def,
          COND_RATOR, vfmTypesTheory.sum_CASE_rator, AllCaseEqs()] >>
      metis_tac[])
QED

Theorem source_call_external_function_trace_result_ok:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  (!cx es st r u.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_exprs cx es st = (r,u) ==>
     source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok r) /\
  (!cx ss st r u.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_stmts cx ss st = (r,u) ==>
     source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok r) /\
  call_external_function_trace (SOME os) gobs am cx nr mut ts mods args dflts vals stmts ret =
    (res,am_out,rqs,obs) ==>
  total_balance am_out.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_trace_def, Excl "lock_if_nr_def",
       Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  Cases_on `LENGTH vals > LENGTH args \/ LENGTH args - LENGTH vals > LENGTH dflts` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
  >- (strip_tac >> gvs[balance_place_ok]) >>
  Cases_on `if cx.in_deploy then evaluate_module_constants_trace cx am cx.txn.target
    (constants_order mods) else (SOME am, [])` >>
  rename1 `(if cx.in_deploy then _ else _) = (constants,constant_trace)` >>
  Cases_on `constants` >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
  >- (strip_tac >> gvs[balance_place_ok]) >>
  rename1 `(if cx.in_deploy then _ else _) = (SOME am_c,constant_trace)` >>
  `am_c.accounts = am.accounts` by
    (Cases_on `cx.in_deploy` >> gvs[] >>
     `evaluate_all_constants cx am cx.txn.target mods = SOME am_c` by
       simp[evaluate_all_constants_def, evaluate_module_constants_def] >>
     drule vyperConstantsStorageFrameTheory.evaluate_all_constants_machine_frame >>
     disch_then (fn th => simp[Once th])) >>
  qmatch_goalsub_abbrev_tac `ignore_bind (send_call_value mut cx) rest s0` >>
  `source_balance_bounded (2 ** 256 - 1) s0` by
    (simp[Abbr `s0`, initial_state_def, source_balance_bounded_def] >> (gvs[])) >>
  `^balance_place_unit (send_call_value mut cx)` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >>
     Cases_on `cx.txn.value = 0` >> Cases_on `mut = Payable` >>
     gvs[send_call_value_def, ignore_bind_def, bind_def, check_def,
         assert_def, return_def, raise_def, balance_place_ok] >>
     conj_tac
     >- (irule source_transfer_value_preserves_bound >> simp[] >> metis_tac[]) >>
     irule (SIMP_RULE (srw_ss()) [balance_place_ok]
       source_transfer_value_no_recipient_overflow) >> simp[] >> metis_tac[]) >>
  pop_assum $ mk_asm "send" >>
  `!es. ^(balance_place_as ``:value list``) (eval_external_defaults cx es)` by
    (BETA_TAC >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `eval_external_defaults _ _ _ = _` mp_tac >>
     simp[eval_external_defaults_run] >>
     Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
     simp[] >> strip_tac >> gvs[] >>
     `source_balance_bounded (2 ** 256 - 1) (st with scopes := [FEMPTY])` by
       gvs[source_balance_bounded_def] >>
     gvs[] >>
     qpat_assum `!cx es st r u. _ /\ eval_exprs cx es st = (r,u) ==> _` drule_all >>
     gvs[source_balance_bounded_def]) >>
  pop_assum $ mk_asm "defaults" >>
  `^balance_place_unit (ignore_bind (send_call_value mut cx) rest)` by
    (simp_tac bool_ss [Abbr `rest`] >>
     qpat_assum `!cx ss st r u. _ /\ eval_stmts cx ss st = (r,u) ==> _`
       (fn eval_stmts_safe => asm "send" (fn send => asm "defaults" (fn defaults =>
         BALANCE_PLACE_WALK
           [send, defaults, source_balance_ordinary_primitives, eval_stmts_safe] [])))) >>
  Cases_on `ignore_bind (send_call_value mut cx) rest s0` >>
  rename1 `ignore_bind (send_call_value mut cx) rest s0 = (out,u)` >>
  `source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok out` by
    (qpat_assum `^balance_place_unit (ignore_bind (send_call_value mut cx) rest)` mp_tac >>
     BETA_TAC >> disch_then drule_all >> simp[]) >>
  Cases_on `unlock_if_nr cx nr (is_view_mut mut) u` >>
  rename1 `unlock_if_nr cx nr (is_view_mut mut) u = (unl,w)` >>
  `source_balance_bounded (2 ** 256 - 1) w /\ source_result_ok unl` by
    FIRST (map (fn th => drule_all th >> (simp[] >> NO_TAC))
      (CONJUNCTS source_balance_ordinary_primitives)) >>
  qpat_x_assum `source_result_ok out` (assume_tac o REWRITE_RULE[balance_place_ok]) >>
  qpat_x_assum `source_result_ok unl` (assume_tac o REWRITE_RULE[balance_place_ok]) >>
  `total_balance (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts u).accounts <=
     2 ** 256 - 1` by
    (irule source_balance_bounded_abstract_machine >> first_assum ACCEPT_TAC) >>
  `total_balance (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts w).accounts <=
     2 ** 256 - 1` by
    (irule source_balance_bounded_abstract_machine >> first_assum ACCEPT_TAC) >>
  Cases_on `out`
  >- (Cases_on `unl` >>
      simp[balance_place_ok, Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
      disch_then strip_assume_tac >>
      rule_assum_tac (REWRITE_RULE[sumTheory.INR_11]) >>
      gvs[abstract_machine_from_state_def, source_balance_bounded_def]) >>
  rename1 `ignore_bind (send_call_value mut cx) rest s0 = (INR exc,u)` >>
  Cases_on `exc` >> Cases_on `unl` >>
  simp[balance_place_ok, Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  simp_tac bool_ss [pairTheory.UNCURRY, pairTheory.PAIR] >>
  simp[AllCaseEqs()] >> disch_then strip_assume_tac >>
  (qpat_x_assum `_ = res` (SUBST1_TAC o SYM) ORELSE
   qpat_x_assum `res = _` SUBST1_TAC) >>
  rule_assum_tac (REWRITE_RULE[sumTheory.INR_11, vyperStateTheory.exception_11]) >> simp[] >>
  FIRST [drule_all abstract_machine_balance_eq,
         drule_all machine_balance_eq] >> simp[]
QED

Theorem balance_eval_try[local]:
  source_balance_bounded B st /\
  (!r mid. source_balance_bounded B st /\ f st = (r,mid) ==>
    source_balance_bounded B mid /\ source_result_ok r) /\
  (!e mid r t. f st = (INR e,mid) /\ source_balance_bounded B mid /\
    source_result_ok (INR e) /\ h e mid = (r,t) ==>
    source_balance_bounded B t /\ source_result_ok r) /\
  try f h st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  rpt gen_tac >> strip_tac >> namedCases_on `f st` ["r mid"] >>
  Cases_on `r` >> gvs[try_def, source_result_ok_def]
QED

Theorem balance_eval_transfer[local]:
  source_balance_bounded (2 ** 256 - 1) st /\
  transfer_value src dst amount st = (res,st') ==>
  source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res
Proof
  strip_tac >> conj_tac
  >- (irule source_transfer_value_preserves_bound >> metis_tac[]) >>
  irule source_transfer_value_no_recipient_overflow >> metis_tac[]
QED

Theorem balance_eval_self_codesize[local]:
  !cx vs. vyperContext$evaluate_self_codesize cx vs <>
    INR (RuntimeError "transfer_value recipient overflow")
Proof
  gen_tac >> Cases >> simp[vyperContextTheory.evaluate_self_codesize_def] >>
  Cases_on `h` >> Cases_on `t` >> simp[vyperContextTheory.evaluate_self_codesize_def]
QED

Theorem balance_eval_return_raise[local]:
  (source_balance_bounded B st /\ return v st = (res,st') ==>
    source_balance_bounded B st' /\ source_result_ok res) /\
  (source_balance_bounded B st /\ raise e st = (r,t) /\
    e <> Error (RuntimeError "transfer_value recipient overflow") ==>
    source_balance_bounded B t /\ source_result_ok r)
Proof
  conj_tac >- (simp[return_def] >> strip_tac >> gvs[source_result_ok_def]) >>
  simp[raise_def] >> strip_tac >> gvs[] >>
  Cases_on `e` >> gvs[source_result_ok_def] >>
  Cases_on `e'` >> gvs[source_result_ok_def]
QED

(* Select rules on the witnessed execution, not the common postcondition. *)

local
  val exclusions = CONJUNCTS vyperPureReadingErrorsTheory.pure_overflow_error_exclusions
  val places = MP source_balance_place_primitives (LIST_CONJ (List.drop (exclusions,6)))
  val combinators = [source_balance_walk_bind, balance_eval_try,
      source_balance_walk_finally, source_balance_walk_finally_unless_halt]
  val leaves = [source_balance_ordinary_primitives, source_balance_walk_lifts,
      places, balance_eval_transfer, source_balance_zero_account, balance_eval_return_raise]
  val curry = PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]
  fun is_run tm = is_eq tm andalso pairSyntax.is_pair (rhs tm)
  fun is_post tm = is_conj tm andalso can (match_term ``source_result_ok r``) (rand tm)
  fun split th =
    let val w = concl th in
      if is_forall w then split (SPEC_ALL th)
      else if is_post w then [th]
      else if is_conj w then split (CONJUNCT1 th) @ split (CONJUNCT2 th)
      else if is_imp_only w then map (DISCH (lhand w)) (split (UNDISCH th))
      else []
    end
  fun rule th =
    let val h = curry th
        val (ants,_) = strip_imp (concl h)
        val runs = List.filter is_run ants
        (* The final run, when an IH also has successful-prefix equations. *)
        val run = List.last runs
        val prems = List.filter (not o aconv run) ants
        val pre = ASSUME (list_mk_conj prems)
        val body = DISCH run (UNDISCH_ALL h)
        val key = fst (strip_comb (lhs run))
    in (key, DISCH (concl pre) (itlist PROVE_HYP (CONJUNCTS pre) body)) end
  fun rules th = List.mapPartial (total rule) (split (CONV_RULE (DEPTH_CONV BETA_CONV) th))
  val fixed = List.concat (map rules (combinators @ leaves))
  fun run_goal w = is_imp_only w andalso is_run (lhand w) andalso is_post (rand w)
  (* Guard witnesses can occur only in earlier run equations. Resolve those
     equations in order, after matching the computation of interest. *)
  fun guarded th (g as (asl,w)) ctxt =
    let val facts = exclusions @ map ASSUME asl
        val vs = List.filter (fn v => not (HOLset.member (hyp_frees th,v)))
          (free_vars (concl th))
        val fresh = map (genvar o type_of) vs
        val th = INST (ListPair.map (op |->) (vs,fresh)) th
        fun discharge h =
          if run_goal (concl h) then ACCEPT_TAC h
          else
            let val p = lhand (concl h)
                val refs = (if is_eq p then [REFL (lhs p), REFL (rhs p)] else []) @
                  mapfilter (EQT_ELIM o SIMP_CONV bool_ss []) [p]
                val fixed_vars = FVL [w] (hyp_frees h)
                fun feed fact = MP (INST_TY_TERM
                  (match_terml [] fixed_vars p (concl fact)) h) fact
                val next = List.mapPartial (total feed) (refs @ facts)
            in FIRST (map discharge next) end
    in discharge (curry (PART_MATCH rand th w)) g ctxt end
  fun apply_rules (g as (asl,w)) =
    let val k = fst (strip_comb (lhs (lhand w)))
        val live = List.concat (map (rules o ASSUME) (List.filter is_forall asl))
        fun select ts = map snd (List.filter (fn (head,_) => same_const head k) ts)
    in FIRST (map MATCH_MP_TAC (select fixed) @ map guarded (select live)) g end
  val at = LAND_CONV o LHS_CONV
  fun on_run tac (g as (_,w)) = if run_goal w then tac g else NO_TAC g
  fun intro (g as (_,w)) =
    (if is_forall w then gen_tac else if is_imp_only w andalso not (run_goal w)
     then strip_tac else NO_TAC) g
  val unfold = evalWalkLib.unfold_conv [ignore_bind_def,switch_BoolV_def]
  val atomic = CHANGED_TAC (simp_tac bool_ss
    ([vyperStateTheory.exception_distinct, vyperStateTheory.exception_11,
      vyperValueOperationTheory.error_distinct, vyperValueOperationTheory.error_11,
      balance_eval_self_codesize] @ exclusions))
  val normalize = [create_kind_11, create_kind_distinct, GSYM create_kind_distinct,
    COND_CLAUSES, pairTheory.FST, pairTheory.SND]
  fun solve_atomic (g as (_,w)) =
    if run_goal w then NO_TAC g
    else if can (match_term ``source_result_ok (INR e)``) w then
      (simp_tac bool_ss [source_result_ok_def, sumTheory.sum_case_def] >>
       first_assum (ACCEPT_TAC o SIMP_RULE bool_ss
         [source_result_ok_def, sumTheory.sum_case_def])) g
    else atomic g
  val step = FIRST [first_assum ACCEPT_TAC, intro,
    on_run apply_rules, conj_tac, on_run (CONV_TAC (at unfold)),
    on_run (CONV_TAC (at (CHANGED_CONV evalWalkLib.head_conv))), solve_atomic,
    CONV_TAC (RAND_CONV (CHANGED_CONV stringLib.string_EQ_CONV)),
    on_run evalWalkLib.HEAD_CASE_TAC]
in
  val BALANCE_EVAL_WALK = rpt step;
  val BALANCE_EVAL_CASE =
    PURE_REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt intro >>
    simp_tac bool_ss [Once evaluate_def] >>
    RULE_ASSUM_TAC (REWRITE_RULE normalize) >> BALANCE_EVAL_WALK;
end;

Theorem source_balance_bounded_cases:
  source_balance_bounded B st ==>
  ?os. st.outcomes = SOME os /\ total_balance st.accounts <= B /\
       EVERY (\co. total_balance co.co_accounts <= B) os
Proof
  simp[source_balance_bounded_def]
QED

Theorem source_balance_take_create:
  kind <> MessageCall /\ kind <> DelegateMessageCall /\
  source_balance_bounded B st /\
  take_create_outcome kind value initcode st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res /\
  (res = INL (rq,outcome) ==> total_balance outcome.co_accounts <= B)
Proof
  strip_tac >> drule source_balance_bounded_cases >> strip_tac >>
  `source_balance_bounded B st'` by
    (rw[source_balance_bounded_def] >>
     drule_all take_create_outcome_suffix >> strip_tac >>
     qexists_tac `rest` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (drule take_create_outcome_frame >> strip_tac >>
       qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
     gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `res`
  >- (Cases_on `x` >> simp[source_result_ok_def] >> strip_tac >>
      drule take_create_outcome_success >> strip_tac >>
      gvs[] >> Cases_on `os`
      >- (gvs[take_create_outcome_def])
      >- (`take_outcome (create_outcome_request kind value initcode st)
            (h::t) = (h,t)` by
            (gvs[create_outcome_request_def, extCallOracleTheory.take_outcome_create]) >>
          gvs[]))
  >- (drule take_create_outcome_error >> strip_tac >>
      gvs[source_result_ok_def])
QED

Theorem source_balance_create_oracle:
  source_balance_bounded B st /\
  create_oracle_result salt value code rof st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  strip_tac >>
  Cases_on `take_create_outcome
    (case salt of NONE => extCallOracle$CreateCall
                | SOME s => extCallOracle$Create2Call s)
    value code st` >>
  rename1 `take_create_outcome _ _ _ st = (take_res,mid)` >>
  qpat_x_assum `create_oracle_result _ _ _ _ _ = _` mp_tac >>
  simp[vyperCreateTheory.create_oracle_result_def] >> strip_tac >>
  Cases_on `take_res`
  >- (Cases_on `x` >> gvs[] >>
      `source_balance_bounded B mid /\
       total_balance r.co_accounts <= B` by
        (`(case salt of NONE => extCallOracle$CreateCall
                     | SOME s => extCallOracle$Create2Call s) <> MessageCall /\
          (case salt of NONE => extCallOracle$CreateCall
                     | SOME s => extCallOracle$Create2Call s) <> DelegateMessageCall` by
           (Cases_on `salt` >> simp[]) >>
         drule_all source_balance_take_create >> strip_tac >>
         first_x_assum (qspecl_then [`q`,`r`] mp_tac) >>
         gvs[source_result_ok_def]) >>
      `source_balance_bounded B
         (SND (adopt_call_outcome q r mid))` by
        (`adopt_call_outcome q r mid =
             (INL (),SND (adopt_call_outcome q r mid))` by
           rw[adopt_call_outcome_equation] >>
         drule_all source_adopt_call_outcome_preserves_bound >> gvs[]) >>
      gvs[AllCaseEqs(), source_result_ok_def])
  >- (`source_balance_bounded B mid` by
        (`(case salt of NONE => extCallOracle$CreateCall
                     | SOME s => extCallOracle$Create2Call s) <> MessageCall /\
          (case salt of NONE => extCallOracle$CreateCall
                     | SOME s => extCallOracle$Create2Call s) <> DelegateMessageCall` by
           (Cases_on `salt` >> simp[]) >>
         drule_all source_balance_take_create >>
         gvs[source_result_ok_def]) >>
      drule take_create_outcome_error >> strip_tac >>
      gvs[source_result_ok_def])
QED

Theorem source_balance_eval_create:
  source_balance_bounded B st /\
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_balance_bounded B st` mp_tac >>
  simp[source_balance_bounded_def] >> strip_tac >>
  qpat_x_assum `eval_create _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- ((simp[vyperCreateTheory.eval_create_def, bind_def, ignore_bind_def,
           lift_option_type_def, get_accounts_def, check_def, assert_def,
           check_not_static_def, return_def, raise_def, source_balance_bounded_def,
           source_result_ok_def]) >> (metis_tac[]))
  >- (rename1 `SOME ops` >>
      simp[vyperCreateTheory.eval_create_def, bind_def, ignore_bind_def,
           lift_option_type_def, get_accounts_def, check_def, assert_def,
           check_not_static_def, return_def, raise_def] >>
      Cases_on `create_arg_ctor_types kind has_salt arg_tys`
      >- ((simp[bind_def, ignore_bind_def, return_def, raise_def,
                source_balance_bounded_def, source_result_ok_def]) >> metis_tac[])
      >- (rename1 `SOME ctor_tys` >>
          simp[bind_def, ignore_bind_def, return_def, raise_def] >>
          Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size`
          >- ((simp[bind_def, ignore_bind_def, return_def, raise_def,
                    source_balance_bounded_def, source_result_ok_def]) >> metis_tac[])
          >- (rename1 `SOME code_info` >>
              simp[bind_def, ignore_bind_def, return_def, raise_def] >>
              rpt strip_tac >>
              Cases_on `code_info.cc_source_ok` >>
              Cases_on `code_info.cc_size_ok` >>
              Cases_on `cx.txn.is_static` >>
              gvs[check_def, check_not_static_def, source_balance_bounded_def,
                  source_result_ok_def] >>
              `source_balance_bounded B st` by
                (simp[source_balance_bounded_def] >>
                 qexists_tac `os` >> simp[]) >>
              drule_all source_balance_create_oracle >>
              strip_tac >>
              drule source_balance_bounded_cases >>
              strip_tac
              >- (qexists_tac `os'` >> gvs[])
              >- (gvs[source_result_ok_def]))))
QED

Theorem source_balance_eval_create_operands:
  source_balance_bounded B st /\
  eval_create_operands cx kind has_salt rof arg_tys literal_offset vs st = (res,st') ==>
  source_balance_bounded B st' /\ source_result_ok res
Proof
  Cases_on `kind` >>
  simp[vyperCreateTheory.eval_create_operands_def, bind_def, AllCaseEqs()] >>
  disch_then strip_assume_tac >>
  TRY (drule_all source_balance_eval_create >> simp[] >> NO_TAC) >>
  drule check_create_blueprint_result_state >> strip_tac >> gvs[raise_def] >>
  TRY (drule_all source_balance_eval_create >> simp[] >> NO_TAC) >>
  qpat_x_assum `check_create_blueprint _ _ _ _ = _` mp_tac >>
  simp[vyperCreateTheory.check_create_blueprint_def, bind_def, get_accounts_def,
       lift_option_def, return_def] >>
  CASE_TAC >> simp[return_def, raise_def, source_result_ok_def]
QED


Theorem source_balance_bounded_evaluate_mutual_if_wrappers:
  ((!bt vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     precompile_call_success bt vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
   (!cx has_gas vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_send cx has_gas vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
   (!cx flags target_addr calldata amount gas st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_raw_call cx flags target_addr calldata amount gas st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
   (!cx is_static skip_check sig opts vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     (!tenv ret_type returnData.
       evaluate_abi_decode_return tenv ret_type returnData <>
         INR "transfer_value recipient overflow") /\
     eval_ext_call cx is_static skip_check sig opts vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
   (!cx kind has_salt rof arg_tys literal_offset vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_create_operands cx kind has_salt rof arg_tys literal_offset vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res)) ==>
  ((!cx s st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_stmt cx s st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx ss st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_stmts cx ss st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx it st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_iterator cx it st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx tyv nm body vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_for cx tyv nm body vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx e st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_expr cx e st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx es st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_exprs cx es st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx bt st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_base_place cx bt st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx bt st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_target_place cx bt st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx g v st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ assign_tuple_targets cx g v st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx gs vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ assign_tuple_target_list cx gs vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res))
Proof
  strip_tac >> ho_match_mp_tac evaluate_ind >>
  (* Keep each proof step confined to a small batch of constructors. *)
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  ntac 5 (conj_tac >- BALANCE_EVAL_CASE) >>
  rpt conj_tac >> BALANCE_EVAL_CASE
QED

Theorem source_balance_bounded_evaluate_mutual:
  (!cx s st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_stmt cx s st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx ss st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_stmts cx ss st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx it st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_iterator cx it st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx tyv nm body vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_for cx tyv nm body vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx e st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_expr cx e st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx es st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_exprs cx es st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx bt st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_base_place cx bt st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx bt st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_target_place cx bt st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx g v st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ assign_tuple_targets cx g v st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res) /\
  (!cx gs vs st res st'.
     source_balance_bounded (2 ** 256 - 1) st /\ assign_tuple_target_list cx gs vs st = (res,st') ==>
     source_balance_bounded (2 ** 256 - 1) st' /\ source_result_ok res)
Proof
  irule source_balance_bounded_evaluate_mutual_if_wrappers >>
  rpt conj_tac
  >- ((metis_tac[CONJUNCT1 source_balance_oracle_call_primitives]))
  >- (metis_tac[CONJUNCT2 source_balance_oracle_call_primitives])
  >- ((metisTools.METIS_TAC [DB.fetch "vyperBalanceOverflow" "source_balance_oracle_call_primitives"]))
  >- ((boolLib.MATCH_ACCEPT_TAC (DB.fetch "vyperBalanceOverflow" "source_balance_eval_create_operands")))
  >- (metisTools.METIS_TAC [DB.fetch "vyperBalanceOverflow" "source_balance_oracle_call_primitives"])
QED

Theorem source_call_external_function_trace_result_ok_error:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  (!cx es st r u.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_exprs cx es st = (r,u) ==>
     source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok r) /\
  (!cx ss st r u.
     source_balance_bounded (2 ** 256 - 1) st /\
     eval_stmts cx ss st = (r,u) ==>
     source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok r) /\
  call_external_function_trace (SOME os) gobs am cx nr mut ts mods args dflts vals stmts ret =
    (INR (Error e),am_out,rqs,obs) ==>
  total_balance am_out.accounts <= 2 ** 256 - 1 /\ source_result_ok (INR (Error e))
Proof
  strip_tac >>
  drule_at (Pos last) source_call_external_function_trace_result_ok >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[source_result_ok_def]
QED

Theorem source_call_external_no_recipient_overflow:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  call_external_trace (SOME os) gobs am tx = (res,am',rqs,obs) ==>
  total_balance am'.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  qpat_x_assum `call_external_trace _ _ _ _ = _` mp_tac >>
  simp[call_external_trace_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx
    (find_function_module am tx.target tx.function_name)` >>
  Cases_on `ALOOKUP am.sources tx.target`
  >- (simp[source_result_ok_def] >> strip_tac >> gvs[]) >>
  rename1 `ALOOKUP am.sources tx.target = SOME mods` >>
  Cases_on `case find_function_module am tx.target tx.function_name of
              NONE => get_self_code cx
            | SOME src_id => get_module_code cx (SOME src_id)`
  >- (simp[source_result_ok_def] >> strip_tac >> gvs[]) >>
  rename1 `_ = SOME ts` >>
  Cases_on `lookup_exported_function cx am tx.function_name`
  >- (simp[source_result_ok_def] >> strip_tac >> gvs[]) >>
  rename1 `lookup_exported_function _ _ _ = SOME fields` >>
  PairCases_on `fields` >>
  Cases_on `call_external_function_trace (SOME os) gobs am cx fields1 fields0
    ts mods fields2 fields3 tx.args fields5 fields4` >>
  PairCases_on `r` >> gvs[] >>
  Cases_on `q`
  >- (strip_tac >>
      drule_at (Pos last) source_call_external_function_trace_result_ok >>
      (impl_tac >- (rpt conj_tac >>
        FIRST [MATCH_ACCEPT_TAC (List.nth
                 (CONJUNCTS source_balance_bounded_evaluate_mutual,5)),
               MATCH_ACCEPT_TAC (List.nth
                 (CONJUNCTS source_balance_bounded_evaluate_mutual,1)),
               simp[]])) >>
      simp[balance_place_ok] >>
      rpt strip_tac >>
      gvs[] >>
      drule_all finalize_pending_deletions_balance_bounded >>
      gvs[] >> simp[]) >>
  `total_balance r0.accounts <= 2 ** 256 - 1 /\ source_result_ok (INR y)` by
    (drule_at (Pos last) source_call_external_function_trace_result_ok >>
     (impl_tac >- (rpt conj_tac >>
       FIRST [MATCH_ACCEPT_TAC (List.nth
                (CONJUNCTS source_balance_bounded_evaluate_mutual,5)),
              MATCH_ACCEPT_TAC (List.nth
                (CONJUNCTS source_balance_bounded_evaluate_mutual,1)),
              simp[]])) >>
     simp[balance_place_ok]) >>
  Cases_on `y` >> gvs[balance_place_ok] >>
  rpt strip_tac >>
  FIRST [gvs[] >> NO_TAC,
         qpat_x_assum `finalize_pending_deletions r0 = am'`
           (fn th => REWRITE_TAC [GSYM th]) >>
         irule finalize_pending_deletions_balance_bounded >>
         qpat_x_assum `total_balance r0.accounts <= _`
           (fn th => MATCH_ACCEPT_TAC th)]
QED

Theorem source_call_external_no_recipient_overflow_public:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  call_external (SOME os) gobs am tx = (res,am',rqs) ==>
  total_balance am'.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >>
  Cases_on `call_external_trace (SOME os) gobs am tx` >>
  PairCases_on `r` >>
  gvs[call_external_def] >>
  drule_at (Pos last) source_call_external_no_recipient_overflow >>
  gvs[]
QED

Theorem source_call_external_function_trace_result_ok_updated[local]:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  (!cx es st r u.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_exprs cx es st = (r,u) ==>
     source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok r) /\
  (!cx ss st r u.
     source_balance_bounded (2 ** 256 - 1) st /\ eval_stmts cx ss st = (r,u) ==>
     source_balance_bounded (2 ** 256 - 1) u /\ source_result_ok r) /\
  call_external_function_trace (SOME os) gobs
    (am with <|exports updated_by CONS (target,exps);
                immutables updated_by CONS (target,imms)|>)
    cx nr mut ts mods args dflts vals stmts ret = (res,am_out,rqs,obs) ==>
  total_balance am_out.accounts <= 2 ** 256 - 1 /\ source_result_ok res
Proof
  strip_tac >> irule source_call_external_function_trace_result_ok >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (irule_at Any) >> gvs[]
QED

Theorem source_load_contract_no_recipient_overflow:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  load_contract_trace (SOME os) gobs am tx mods exps = (res,obs) ==>
  source_result_ok res /\
  (!am' rqs. res = INL (am',rqs) ==>
     total_balance am'.accounts <= 2 ** 256 - 1)
Proof
  strip_tac >>
  qpat_x_assum `load_contract_trace _ _ _ _ _ _ = _` mp_tac >>
  simp[load_contract_trace_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods`
  >- simp[source_result_ok_def] >>
  rename1 `initial_immutables (type_env_all_modules mods) mods = SOME imms` >>
  Cases_on `lookup_function NONE tx.function_name Deploy
      (case ALOOKUP mods NONE of NONE => [] | SOME ts => ts)`
  >- simp[source_result_ok_def] >>
  rename1 `lookup_function NONE tx.function_name Deploy _ = SOME fields` >>
  PairCases_on `fields` >>
  Cases_on `call_external_function_trace (SOME os) gobs
    (am with <|exports updated_by CONS (tx.target,exps);
                immutables updated_by CONS (tx.target,imms)|>)
    ((initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
      (tx with created_in_tx := T) NONE) with in_deploy := T)
    fields1 fields0 (case ALOOKUP mods NONE of NONE => [] | SOME ts => ts)
    mods fields2 fields3 tx.args fields5 fields4` >>
  PairCases_on `r` >> gvs[] >>
  `total_balance r0.accounts <= 2 ** 256 - 1 /\ source_result_ok q` by
    (drule_at (Pos last) source_call_external_function_trace_result_ok_updated >>
     impl_tac
     >- (rpt conj_tac >>
         FIRST [MATCH_ACCEPT_TAC (List.nth
                  (CONJUNCTS source_balance_bounded_evaluate_mutual,5)),
                MATCH_ACCEPT_TAC (List.nth
                  (CONJUNCTS source_balance_bounded_evaluate_mutual,1)),
                simp[]]) >>
     simp[]) >>
  Cases_on `q`
  >- (simp[] >> strip_tac >> gvs[source_result_ok_def] >>
      irule finalize_pending_deletions_balance_bounded >>
      irule source_machine_sources_update_balance >>
      qpat_x_assum `total_balance r0.accounts <= _`
        (fn th => MATCH_ACCEPT_TAC th)) >>
  rename1 `source_result_ok (INR exc)` >>
  Cases_on `exc` >> simp[] >> strip_tac >> gvs[balance_place_ok] >>
  FIRST [gvs[] >> NO_TAC,
         irule finalize_pending_deletions_balance_bounded >>
         qpat_x_assum `total_balance r0.accounts <= _`
           (fn th => MATCH_ACCEPT_TAC th)]
QED

Theorem source_load_contract_no_recipient_overflow_public:
  total_balance am.accounts <= 2 ** 256 - 1 /\
  EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1) os /\
  load_contract (SOME os) gobs am tx mods exps = res ==>
  source_result_ok res /\
  (!am' rqs. res = INL (am',rqs) ==>
     total_balance am'.accounts <= 2 ** 256 - 1)
Proof
  strip_tac >>
  Cases_on `load_contract_trace (SOME os) gobs am tx mods exps` >>
  gvs[load_contract_def] >>
  drule_at (Pos last) source_load_contract_no_recipient_overflow >>
  gvs[]
QED

val () = monadsyntax.enable_monad "vyper_evaluation";
