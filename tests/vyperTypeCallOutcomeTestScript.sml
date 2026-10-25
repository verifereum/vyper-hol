(* Focused typed boundary clients of the current Send/ExtCall helpers. *)
Theory vyperTypeCallOutcomeTest
Ancestors
  list option pair sum arithmetic words finite_map
  vyperMisc vyperAST vyperValue vyperState vyperInterpreter vyperABI vyperTyping
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
  rpt gen_tac >> strip_tac >> drule Send_outcome_runtime_error >>
  rw[no_control_exc_def]
QED

(* Typed operands are required by eval_ext_call; functions_well_typed is
   not: the callee is outside the source function environment. *)
Theorem ExtCall_decode_type_client:
  runtime_consistent env cx st /\
  exprs_runtime_typed env es vs /\
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
  rpt strip_tac >> drule_all eval_ext_call_result_sound >> simp[]
QED

Theorem ExtCall_decode_no_control:
  eval_ext_call cx stat skc fsig opts vs st = (INR exc,st') ==>
  no_control_exc exc
Proof
  rpt strip_tac >> drule eval_ext_call_no_control >> simp[]
QED

(* Skip the code guard to isolate the post-adoption decoder. No default is
   supplied: malformed bytes really run the decoder, even on empty data. *)
val extcall_boundary_simps =
  [eval_ext_call_def, ext_call_opts_ok_def, ext_call_kwarg_def,
   ext_call_precheck_ok_def, bind_def, ignore_bind_def, return_def, raise_def,
   type_check_def, check_def, assert_def, lift_option_type_def,
   lift_sum_runtime_def, get_accounts_def];

Theorem ExtCall_decode_errors_are_runtime:
  st.outcomes = SOME os /\
  dest_AddressV target_v = SOME target /\ dest_NumV amount_v = SOME amount /\
  build_ext_calldata (get_tenv cx) func_name [] [] = SOME data /\
  take_call_outcome target data (SOME amount) st = (INL (rq,outcome),st1) /\
  outcome.co_success /\ adopt_call_outcome rq outcome st1 = (INL (),st2) /\
  evaluate_abi_decode_return (get_tenv cx) ret_type outcome.co_returnData = INR msg ==>
  eval_ext_call cx F T (func_name,[],ret_type) [EKValue] [target_v;amount_v] st =
    (INR (Error (RuntimeError msg)),st2)
Proof
  rpt strip_tac >> Cases_on `ret_type` >> simp extcall_boundary_simps
QED

(* Failure propagates the actual bytes and does not adopt the outcome. *)
Theorem ExtCall_revert_preserves_payload:
  st.outcomes = SOME os /\
  dest_AddressV target_v = SOME target /\ dest_NumV amount_v = SOME amount /\
  build_ext_calldata (get_tenv cx) func_name [] [] = SOME data /\
  take_call_outcome target data (SOME amount) st = (INL (rq,outcome),st1) /\
  ~outcome.co_success ==>
  eval_ext_call cx F T (func_name,[],ret_type) [EKValue] [target_v;amount_v] st =
    (INR (Error (RevertData outcome.co_returnData)),st1)
Proof
  rpt strip_tac >> Cases_on `ret_type` >> simp extcall_boundary_simps
QED

(* Defaults are already evaluated operands, not expressions to run after
   adoption. Empty return data selects that captured value at the adopted state. *)
Theorem ExtCall_default_selected_after_adoption:
  st.outcomes = SOME os /\
  dest_AddressV target_v = SOME target /\ dest_NumV amount_v = SOME amount /\
  build_ext_calldata (get_tenv cx) func_name [] [] = SOME data /\
  take_call_outcome target data (SOME amount) st = (INL (rq,outcome),st1) /\
  outcome.co_success /\ outcome.co_returnData = [] /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  eval_ext_call cx F T (func_name,[],ret_type) [EKValue;EKDefault]
    [target_v;amount_v;default_v] st = (INL (Value default_v),st2)
Proof
  rpt strip_tac >> Cases_on `ret_type` >> simp extcall_boundary_simps
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
