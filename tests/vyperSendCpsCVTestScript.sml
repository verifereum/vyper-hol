(* Actual Send CPS execution: no evaluator-equivalence rewrites in CV proofs.
   Persistent/transient storage, code, nonce, logs, remaining payloads and
   pre-adoption request snapshots are observed, not just helper parameters. *)
Theory vyperSendCpsCVTest
Ancestors
  vyperExtCallCpsCVTest vyperSmallStep[ignore_grammar] extCallOracle
  vyperCallOutcome[ignore_grammar] vfmState[ignore_grammar]
  vfmExecution[ignore_grammar] vyperState vyperContext vyperAST vyperValue
  list option pair finite_map words vfmTypes
Libs cv_transLib wordsLib

Definition send_call_def:
  send_call target amount = Call NoneT Send
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [target]));
     Literal (BaseT (UintT 256)) (IntL (&amount))] NONE
End
val () = cv_auto_trans send_call_def;

Definition send_state_def:
  send_state = cpscv_state with accounts := update_account 11w
    (empty_account_state with <|balance := 3; storage := update_storage 1w 2w empty_storage|>)
    empty_accounts
End
val () = cv_auto_trans send_state_def;

Definition send_outcome_def:
  send_outcome success data balance = (cpscv_outcome success data balance) with
    co_accounts := update_account 11w (empty_account_state with
      <|balance := balance; nonce := 5; code := [0w];
        storage := update_storage 1w 9w empty_storage|>) empty_accounts
End
val () = cv_auto_trans send_outcome_def;

Definition send_request_fields_def:
  send_request_fields st = MAP (λrq.
    (rq.cr_target,rq.cr_value,rq.cr_data,rq.cr_static,
     (lookup_account 11w rq.cr_accounts).balance,
     lookup_storage 1w (lookup_account 11w rq.cr_accounts).storage,
     lookup_storage 1w (vfmExecution$lookup_transient_storage 11w rq.cr_tStorage))) st.requests
End
val () = cv_auto_trans send_request_fields_def;

Definition send_snapshot_def:
  send_snapshot balance nonce code persistent transient logs rqs rest st <=>
    (lookup_account 11w st.accounts).balance = balance /\
    (lookup_account 11w st.accounts).nonce = nonce /\
    (lookup_account 11w st.accounts).code = code /\
    lookup_storage 1w (lookup_account 11w st.accounts).storage = persistent /\
    lookup_storage 1w (vfmExecution$lookup_transient_storage 11w st.tStorage) = transient /\
    st.logs = logs /\ st.scopes = [FEMPTY] /\ st.immutables = [(11w,[])] /\
    st.pending_deletions = [] /\
    send_request_fields st = rqs /\
    OPTION_MAP (MAP (λco. (co.co_success,co.co_returnData,
      (lookup_account 11w co.co_accounts).balance,
      lookup_storage 1w (vfmExecution$lookup_transient_storage 11w co.co_tStorage),
      co.co_logs, co.co_toDelete)))
      st.outcomes = rest
End
val () = cv_auto_trans send_snapshot_def;

Definition send_initial_requests_def:
  send_initial_requests = [(12w:address,0:num,[]:word8 list,F,0:num,0w:256 word,0w:256 word)]
End
val () = cv_auto_trans send_initial_requests_def;

Definition send_requests_def:
  send_requests target amount = send_initial_requests ++ [(target,amount,[],F,3,2w,4w)]
End
val () = cv_auto_trans send_requests_def;

Definition send_observe_def:
  send_observe target amount os expected balance nonce code persistent transient logs rqs rest =
    let r = cpscv_run (send_call target amount) (send_state with outcomes := os) in
    FST r = expected /\ send_snapshot balance nonce code persistent transient logs rqs rest (SND r)
End
val () = cv_auto_trans send_observe_def;

Theorem send_cps_success_adopts_code_storage_logs:
  send_observe 9w 7 (SOME [send_outcome T [99w] 17; cpscv_tail])
    (INL (Value NoneV)) 17 5 [0w] 9w 8w cpscv_adopted_logs
    (send_requests 9w 7) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_failure_consumes_ignores_bad_payload:
  send_observe 9w 7 (SOME [send_outcome F [] (2 ** 256); cpscv_tail])
    (INR (Error (RuntimeError "send failed"))) 3 0 [] 2w 4w cpscv_initial_logs
    (send_requests 9w 7) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_exhaustion_records_request:
  send_observe 9w 7 (SOME [])
    (INR (Error (RuntimeError "send failed"))) 3 0 [] 2w 4w cpscv_initial_logs
    (send_requests 9w 7) (SOME [])
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_invalid_success_consumes_before_guard_error:
  send_observe 9w 7 (SOME [send_outcome T [] (2 ** 256); cpscv_tail])
    (INR (Error (RuntimeError "call outcome accounts"))) 3 0 [] 2w 4w cpscv_initial_logs
    (send_requests 9w 7) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_NONE_balance_failure_unchanged:
  send_observe 9w 7 NONE
    (INR (Error (RuntimeError "send failed"))) 3 0 [] 2w 4w cpscv_initial_logs
    send_initial_requests NONE
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_NONE_zero_transfer_unchanged:
  send_observe 42w 0 NONE (INL (Value NoneV)) 3 0 [] 2w 4w cpscv_initial_logs
    send_initial_requests NONE
Proof
  CONV_TAC cv_eval
QED

(* Shared computed behavior for all four special addresses; Send has empty
   calldata so the EC cases are valid zero points, not arbitrary oracle heads. *)
Theorem send_cps_computed_no_consumption_no_request:
  EVERY (λtarget. send_observe target 0 (SOME [cpscv_tail])
    (INL (Value NoneV)) 3 0 [] 2w 4w cpscv_initial_logs
    send_initial_requests cpscv_tail_snapshot) [1w;2w;6w;7w]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

(* Nonzero value selects ordinary outcomes even at computed addresses. *)
Theorem send_cps_special_nonzero_uses_ordinary_outcome:
  EVERY (λtarget. send_observe target 7 (SOME [send_outcome T [] 17; cpscv_tail])
    (INL (Value NoneV)) 17 5 [0w] 9w 8w cpscv_adopted_logs
    (send_requests (w2w target) 7) cpscv_tail_snapshot) [1w;2w;6w;7w]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

Definition send_prefix_observe_def:
  send_prefix_observe =
    let e = Call NoneT Send
      [cpscv_call F 9w (BaseT AddressT) NONE;
       cpscv_call F 9w (BaseT (UintT 256)) NONE] NONE in
    let r = cpscv_run e (send_state with outcomes := SOME
      [send_outcome T (REPLICATE 31 0w ++ [9w]) 17;
       send_outcome T (REPLICATE 31 0w ++ [7w]) 23;
       send_outcome F [] 29; cpscv_tail]) in
    FST r = INR (Error (RuntimeError "send failed")) /\
    send_snapshot 23 5 [0w] 9w 8w
      (cpscv_adopted_logs ++ [<|logger := 11w; topics := [1w]; data := [8w]|>])
      (send_initial_requests ++
       [(9w,7,[38w;18w;31w;240w],F,3,2w,4w);
        (9w,7,[38w;18w;31w;240w],F,17,9w,8w);
        (9w,7,[],F,23,9w,8w)]) cpscv_tail_snapshot (SND r)
End
val () = cv_auto_trans send_prefix_observe_def;

Theorem send_cps_prefix_outcomes_and_request_order:
  send_prefix_observe
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_arity_before_arguments:
  cpscv_run (Call NoneT Send [Name (BaseT AddressT) "missing"] NONE)
    (send_state with outcomes := SOME [cpscv_tail]) =
    (INR (Error (TypeError "Send args")),send_state with outcomes := SOME [cpscv_tail])
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_evaluates_all_arguments_before_unwrap:
  cpscv_run (Call NoneT Send
    [Literal (BaseT (UintT 256)) (IntL 7); Name (BaseT (UintT 256)) "missing"] NONE)
    (send_state with outcomes := SOME [cpscv_tail]) =
    (INR (Error (TypeError "Name not in scope")),send_state with outcomes := SOME [cpscv_tail])
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_address_unwrap_before_amount:
  cpscv_run (Call NoneT Send
    [Literal (BaseT (UintT 256)) (IntL 7); Literal (BaseT BoolT) (BoolL T)] NONE)
    (send_state with outcomes := SOME [cpscv_tail]) =
    (INR (Error (TypeError "Send not AddressV")),send_state with outcomes := SOME [cpscv_tail])
Proof
  CONV_TAC cv_eval
QED

Theorem send_cps_amount_unwrap_before_take:
  cpscv_run (Call NoneT Send
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]));
     Literal (BaseT BoolT) (BoolL T)] NONE)
    (send_state with outcomes := SOME [cpscv_tail]) =
    (INR (Error (TypeError "Send not NumV")),send_state with outcomes := SOME [cpscv_tail])
Proof
  CONV_TAC cv_eval
QED

Definition send_bad_code_observe_def:
  send_bad_code_observe =
    let bad = (send_outcome T [] 17) with co_accounts := update_account 11w
      (empty_account_state with code := REPLICATE 24577 0w) empty_accounts in
    let r = cpscv_run (send_call 9w 7) (send_state with outcomes := SOME [bad;cpscv_tail]) in
    FST r = INR (Error (RuntimeError "call outcome accounts")) /\
    send_snapshot 3 0 [] 2w 4w cpscv_initial_logs
      (send_requests 9w 7) cpscv_tail_snapshot (SND r)
End
val () = cv_auto_trans send_bad_code_observe_def;

Theorem send_cps_invalid_code_consumes_before_guard_error:
  send_bad_code_observe
Proof
  CONV_TAC cv_eval
QED
