(* Focused actual boundary clients, not live oracle activation. *)
Theory vyperTypeCallOutcomeTest
Ancestors
  list option pair sum arithmetic words finite_map
  vyperAST vyperValue vyperState vyperInterpreter vyperABI vyperTyping
  vyperRuntimeAccounts vyperCallOutcome vyperCallOutcomeProps vyperCallOutcomeBranches
  vyperCallOutcomeFrame vyperTypeCallOutcome vyperTypeExtCallSoundness
  vyperTypeExprSoundness vyperTypeExprResult vyperTypeSystem vyperTypeInvariants
  vyperExprNoControl vyperCallOutcomeTest
Libs monadsyntax cv_transLib wordsLib

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);
val _ = hide "body";

(* These real helper clients test typed guard rejection, static/failed bad
   payloads, computed/exhausted outcomes, and successful account installation.
   The source account check does not inspect arbitrary storage. *)
Theorem adopted_state_is_source_typed:
  runtime_consistent env cx st /\
  take_call_outcome target data value st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  state_well_typed st2 /\ env_consistent env cx st2 /\
  accounts_well_typed st2.accounts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all take_adopt_call_outcome_runtime_consistent >>
  simp[runtime_consistent_def]
QED

Theorem Send_type_client:
  runtime_consistent env cx st /\
  (do (rq,outcome) <- take_call_outcome target [] (SOME amount);
      check outcome.co_success "send failed";
      adopt_call_outcome rq outcome;
      return (Value NoneV) od) st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >> drule_all Send_outcome_type_sound >> simp[]
QED

Theorem Send_errors_exclude_type_and_control:
  (do (rq,outcome) <- take_call_outcome target [] (SOME amount);
      check outcome.co_success "send failed";
      adopt_call_outcome rq outcome;
      return (Value NoneV) od) st = (INR exc,st') ==>
  no_control_exc exc /\ (!msg. exc <> Error (TypeError msg)) /\
  exc <> BreakException /\ exc <> ContinueException /\
  (!v. exc <> ReturnException v)
Proof
  rpt gen_tac >> strip_tac >> drule Send_outcome_runtime_error >>
  rw[no_control_exc_def]
QED

Theorem ExtCall_decode_type_client:
  runtime_consistent env cx st /\ functions_well_typed cx /\
  evaluate_type env.type_defs ret_type = SOME ret_tv /\
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target data value;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type outcome.co_returnData);
    return (Value v)
  od) st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env (Call ret_type (ExtCall stat skc fsig) es NONE) tv
  | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  drule_at Any (ExtCall_outcome_return_type_sound |> Q.INST [`drv` |-> `NONE`]
    |> SRULE [IS_SOME_DEF, THE_DEF, Once well_typed_expr_def]) >>
  disch_then (qspecl_then [`stat`,`skc`,`ret_tv`,`fsig`,`es`,`env`] mp_tac) >> simp[]
QED

Theorem ExtCall_decode_no_control:
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target data value;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type outcome.co_returnData);
    return (Value v)
  od) st = (INR exc,st') ==>
  no_control_exc exc
Proof
  rpt strip_tac >>
  drule_at Any (ExtCall_outcome_return_no_control |> Q.INST [`drv` |-> `NONE`]
    |> SRULE [IS_SOME_DEF, THE_DEF]) >> simp[]
QED

Theorem ExtCall_decode_errors_are_runtime:
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target data value;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type outcome.co_returnData);
    return (Value v)
  od) st = (INR exc,st') ==> ?msg. exc = Error (RuntimeError msg)
Proof
  strip_tac >> Cases_on `take_call_outcome target data value st` >>
  rename1 `take_call_outcome target data value st = (answer,mid)` >>
  drule (ExtCall_outcome_continue |> INST_TYPE [alpha |-> ``:toplevel_value``]) >>
  disch_then (qspecl_then [`ret_type`,
    `\bs. do v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type bs);
             return (Value v) od`] mp_tac) >>
  strip_tac >>
  Cases_on `ret_type = NoneT /\ NULL (lookup_account target st.accounts).code`
  >- (gvs[] >> simp[]) >> gvs[] >> Cases_on `answer`
  >- (rename1 `INL ro` >> Cases_on `ro` >>
      rename1 `take_call_outcome target data value st = (INL (rq,outcome),mid)` >>
      Cases_on `outcome.co_success` >> gvs[] >>
      Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type outcome.co_returnData` >>
      gvs[lift_sum_runtime_def, bind_def, return_def, raise_def]) >>
  gvs[] >> drule take_call_outcome_error >> rw[] >> simp[]
QED

Theorem ExtCall_default_runs_after_adoption:
  take_call_outcome target data value st = (INL (rq,outcome),st1) /\
  outcome.co_success /\ outcome.co_returnData = [] /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) /\
  ret_type <> NoneT ==>
  (do
    accounts <- get_accounts;
    (if ret_type = NoneT then
      check (~NULL (lookup_account target accounts).code) "ExtCall target has no code"
     else return ());
    (rq,outcome) <- take_call_outcome target data value;
    check outcome.co_success "ExtCall reverted";
    adopt_call_outcome rq outcome;
    if outcome.co_returnData = [] /\ IS_SOME (SOME e) then eval_expr cx e
    else do
      v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type outcome.co_returnData);
      return (Value v)
    od
  od) st = eval_expr cx e st2
Proof
  rpt strip_tac >>
  drule (ExtCall_outcome_continue |> INST_TYPE [alpha |-> ``:toplevel_value``]) >>
  disch_then (qspecl_then [`ret_type`,
    `\bs. if bs = [] then eval_expr cx e
     else do v <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type bs);
             return (Value v) od`] mp_tac) >> simp[]
QED

Theorem source_account_guard_bounds_not_storage:
  account_runtime_well_typed (account with storage := storage') =
    account_runtime_well_typed account /\
  (account_runtime_well_typed account ==>
    account.balance < 2 ** 256 /\ LENGTH account.code <= 24576)
Proof
  simp[account_runtime_well_typed_def]
QED

Theorem actual_decode_success:
  evaluate_abi_decode_return FEMPTY (BaseT (UintT 256))
    (REPLICATE 31 0w ++ [7w]) = INL (IntV 7)
Proof
  CONV_TAC cv_eval
QED

Theorem actual_decode_failure:
  evaluate_abi_decode_return FEMPTY (BaseT (UintT 256)) [] = INR "abi_decode invalid"
Proof
  CONV_TAC cv_eval
QED

Theorem decode_failure_is_runtime_and_unchanged:
  evaluate_abi_decode_return tenv ret_type bs = INR msg ==>
  (do v <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type bs);
      return (Value v) od) st = (INR (Error (RuntimeError msg)),st)
Proof
  simp[lift_sum_runtime_def, bind_def, raise_def]
QED
