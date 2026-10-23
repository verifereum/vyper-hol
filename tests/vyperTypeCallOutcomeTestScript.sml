(* Focused clients of the checked-call and external-call type boundaries. *)
Theory vyperTypeCallOutcomeTest
Ancestors
  list option pair sum arithmetic words finite_map
  vyperAST vyperValue vyperState vyperInterpreter vyperABI vyperTyping
  vyperRuntimeAccounts vyperCallOutcome vyperCallOutcomeBranches
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
  rpt gen_tac >> strip_tac >>
  Cases_on `take_call_outcome target [] (SOME amount) st` >>
  rename1 `take_call_outcome target [] (SOME amount) st = (taken,mid)` >>
  drule Send_outcome_continue >> strip_tac >> gvs[] >>
  Cases_on `taken` >> gvs[AllCaseEqs(), no_control_exc_def] >>
  drule vyperCallOutcomeTheory.take_call_outcome_error >>
  rw[no_control_exc_def]
QED

(* Typed operands include keyword values in their source evaluation order. *)
Theorem ExtCall_decode_type_client:
  runtime_consistent env cx st /\ exprs_runtime_typed env es vs /\
  MAP expr_type es =
    BaseT AddressT :: call_types ++ MAP (ext_call_kw_type ret_type) opts /\
  arg_types_fit call_types arg_types /\
  EVERY (well_formed_type env.type_defs) arg_types /\
  ext_call_opts_ok stat opts /\
  evaluate_type env.type_defs ret_type = SOME ret_tv /\
  eval_ext_call cx stat skc (func_name,arg_types,ret_type) opts vs st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env
      (Call ret_type (ExtCall stat skc (func_name,arg_types,ret_type) opts) es NONE) tv
  | INR _ => T
Proof
  strip_tac >> drule_all eval_ext_call_result_sound >> simp[]
QED

Theorem ExtCall_decode_no_control:
  eval_ext_call cx stat skc sig opts vs st = (INR exc,st') ==>
  no_control_exc exc
Proof
  strip_tac >> drule eval_ext_call_no_control >> simp[]
QED

Theorem ExtCall_typed_errors_exclude_type_and_control:
  runtime_consistent env cx st /\ exprs_runtime_typed env es vs /\
  MAP expr_type es =
    BaseT AddressT :: call_types ++ MAP (ext_call_kw_type ret_type) opts /\
  arg_types_fit call_types arg_types /\
  EVERY (well_formed_type env.type_defs) arg_types /\
  ext_call_opts_ok stat opts /\
  evaluate_type env.type_defs ret_type = SOME ret_tv /\
  eval_ext_call cx stat skc (func_name,arg_types,ret_type) opts vs st = (INR exc,st') ==>
  no_control_exc exc /\ (!msg. exc <> Error (TypeError msg)) /\
  exc <> BreakException /\ exc <> ContinueException /\
  (!v. exc <> ReturnException v)
Proof
  strip_tac >> drule_all eval_ext_call_result_sound >> strip_tac >>
  drule eval_ext_call_no_control >>
  rw[no_type_error_result_def, no_control_exc_def] >>
  gvs[no_type_error_result_def]
QED

(* The shared checked continuation follows adoption; default expressions are
   already evaluated operands when eval_ext_call starts. *)
Theorem checked_continuation_runs_after_adoption:
  take_call_outcome target data value st = (INL (rq,outcome),st1) /\
  outcome.co_success /\ adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  (do
    (rq,outcome) <- take_call_outcome target data value;
    check outcome.co_success msg;
    adopt_call_outcome rq outcome;
    k outcome.co_returnData
  od) st = k outcome.co_returnData st2
Proof
  rpt strip_tac >>
  simp[bind_def, ignore_bind_def, check_def, assert_def, return_def]
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
