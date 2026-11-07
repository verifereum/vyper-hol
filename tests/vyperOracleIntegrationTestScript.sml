(* Public source entry integration after ExtCall/Send activation.
   Reuse the permanent actual-CPS fixtures; do not replay generated suites here.
   Failure requests survive machine rollback; deployment failure intentionally
   exposes only its exception. Defaults share the call oracle; constants
   execute concrete NONE. *)
Theory vyperOracleIntegrationTest
Ancestors
  vyperOracleEntryTest vyperSendCpsCVTest vyperExtCallCpsCVTest
  vyperInterpreter vyperSmallStep vyperCall vyperState vyperContext vyperAST
  vyperValue extCallOracle vfmState vfmExecution finite_map list option pair
Libs cv_transLib wordsLib

Definition integration_body_def:
  integration_body = [Expr (send_call 9w 7); Expr (send_call 10w 7)]
End
val () = cv_auto_trans integration_body_def;

Definition integration_program_def:
  integration_program =
    [FunctionDecl External Nonpayable F F "calls" [] [] NoneT integration_body;
     FunctionDecl Deploy Payable F F "__init__" [] [] NoneT integration_body;
     FunctionDecl External Nonpayable F F "defaults" [("x",NoneT)]
       [send_call 20w 0] NoneT [Expr (send_call 10w 7)]]
End
val () = cv_auto_trans integration_program_def;

Definition integration_machine_def:
  integration_machine = initial_machine_state with
    <|sources := [(11w,[(NONE,integration_program)])];
      accounts := send_state.accounts; tStorage := send_state.tStorage;
      logs := cpscv_initial_logs|>
End
val () = cv_auto_trans integration_machine_def;

Definition integration_tx_def:
  integration_tx name = empty_call_txn with
    <|target := 11w; function_name := name|>
End
val () = cv_auto_trans integration_tx_def;

Definition integration_request_fields_def:
  integration_request_fields rqs = MAP (λrq.
    (rq.cr_target,rq.cr_value,rq.cr_data,rq.cr_static,
     (lookup_account 11w rq.cr_accounts).balance,
     lookup_storage 1w (lookup_account 11w rq.cr_accounts).storage,
     lookup_storage 1w (vfmExecution$lookup_transient_storage 11w rq.cr_tStorage))) rqs
End
val () = cv_auto_trans integration_request_fields_def;

Definition integration_two_requests_def:
  integration_two_requests =
    [(9w:address,7:num,[]:word8 list,F,3:num,2w:256 word,4w:256 word);
     (10w,7,[],F,17,9w,8w)]
End
val () = cv_auto_trans integration_two_requests_def;

Definition integration_machine_snapshot_def:
  integration_machine_snapshot balance persistent transient logs am <=>
    (lookup_account 11w am.accounts).balance = balance /\
    lookup_storage 1w (lookup_account 11w am.accounts).storage = persistent /\
    lookup_storage 1w (vfmExecution$lookup_transient_storage 11w am.tStorage) = transient /\
    am.logs = logs
End
val () = cv_auto_trans integration_machine_snapshot_def;

Definition integration_call_observe_def:
  integration_call_observe fresh os result balance persistent transient logs requests =
    let (r,am,rqs) = if fresh then
      call_external_transaction os [] integration_machine (integration_tx "calls")
      else call_external os [] integration_machine (integration_tx "calls") in
    r = result /\ integration_machine_snapshot balance persistent transient logs am /\
    integration_request_fields rqs = requests
End
val () = cv_auto_trans integration_call_observe_def;

Theorem public_call_failure_preserves_requests_after_adoption:
  integration_call_observe F
    (SOME [send_outcome T [] 17; send_outcome F [] 23])
    (INR (Error (RuntimeError "send failed"))) 3 2w 4w cpscv_initial_logs
    integration_two_requests /\
  integration_call_observe T
    (SOME [send_outcome T [] 17; send_outcome F [] 23])
    (INR (Error (RuntimeError "send failed"))) 3 2w 4w []
    integration_two_requests
Proof
  CONV_TAC cv_eval
QED

Theorem public_call_exhaustion_and_guard_failure_requests:
  integration_call_observe F (SOME [])
    (INR (Error (RuntimeError "send failed"))) 3 2w 4w cpscv_initial_logs
    [(9w,7,[],F,3,2w,4w)] /\
  integration_call_observe F (SOME [send_outcome T [] (2 ** 256)])
    (INR (Error (RuntimeError "call outcome accounts"))) 3 2w 4w cpscv_initial_logs
    [(9w,7,[],F,3,2w,4w)] /\
  integration_call_observe F NONE
    (INR (Error (RuntimeError "send failed"))) 3 2w 4w cpscv_initial_logs []
Proof
  CONV_TAC cv_eval
QED

Theorem public_call_success_request_order:
  integration_call_observe F (SOME [send_outcome T [] 17; send_outcome T [] 23])
    (INL NoneV) 23 9w 8w
    (cpscv_adopted_logs ++ [<|logger := 11w; topics := [1w]; data := [8w]|>])
    integration_two_requests
Proof
  CONV_TAC cv_eval
QED

Definition integration_load_observe_def:
  integration_load_observe =
    let mods = [(NONE,integration_program)] in
    let tx = integration_tx "__init__" in
    let failed = load_contract
      (SOME [send_outcome T [] 17; send_outcome F [] 23]) [] integration_machine tx mods [] in
    let exhausted = load_contract (SOME []) [] integration_machine tx mods [] in
    let loaded = load_contract
      (SOME [send_outcome T [] 17; send_outcome T [] 23]) [] integration_machine tx mods [] in
      failed = INR (Error (RuntimeError "send failed")) /\
      exhausted = INR (Error (RuntimeError "send failed")) /\
      (case loaded of INR _ => F | INL (am,rqs) =>
        integration_machine_snapshot 23 9w 8w
          (cpscv_adopted_logs ++ [<|logger := 11w; topics := [1w]; data := [8w]|>]) am /\
        integration_request_fields rqs = integration_two_requests /\
        LENGTH am.sources = 2)
End
val () = cv_auto_trans integration_load_observe_def;

Theorem public_load_success_requests_and_failure_exception:
  integration_load_observe
Proof
  CONV_TAC cv_eval
QED

Definition integration_defaults_constants_observe_def:
  integration_defaults_constants_observe =
    let (r,am,rqs) = call_external
      (SOME [send_outcome T [] 17; send_outcome T [] 23]) []
      integration_machine (integration_tx "defaults") in
    let mods = [(NONE,
      [VariableDecl Private (Constant (send_call 20w 0)) "c" NoneT NONE;
       FunctionDecl Deploy Payable F F "__init__" [] [] NoneT [Expr (send_call 10w 7)]])] in
    let loaded = load_contract (SOME [send_outcome T [] 17]) []
      integration_machine (integration_tx "__init__") mods [] in
    r = INL NoneV /\
    integration_request_fields rqs =
      [(20w,0,[],F,3,2w,4w); (10w,7,[],F,17,9w,8w)] /\
    integration_machine_snapshot 23 9w 8w
      (cpscv_adopted_logs ++ [<|logger := 11w; topics := [1w]; data := [8w]|>]) am /\
    (case loaded of INR _ => F | INL (am,rqs) =>
      integration_request_fields rqs = [(10w,7,[],F,3,2w,4w)] /\
      integration_machine_snapshot 17 9w 8w cpscv_adopted_logs am)
End
val () = cv_auto_trans integration_defaults_constants_observe_def;

Theorem defaults_share_body_oracle_constants_do_not:
  integration_defaults_constants_observe
Proof
  CONV_TAC cv_eval
QED

Definition integration_raw_call_observe_def:
  integration_raw_call_observe delegate rof outsize target os expected rest rqs =
    let e = Call NoneT (RawCallTarget
      <|rcf_is_static := ~delegate; rcf_is_delegate := delegate;
        rcf_revert_on_failure := rof; rcf_max_outsize := outsize;
        rcf_kws := []|>)
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [target]));
       Literal (BaseT (BytesT (Dynamic 1))) (BytesL [])] NONE in
    let r = cpscv_run e (send_state with outcomes := os) in
      FST r = expected /\
      OPTION_MAP LENGTH (SND r).outcomes = rest /\
      send_request_fields (SND r) = rqs
End
val () = cv_auto_trans integration_raw_call_observe_def;

Definition integration_raw_call_requests_def:
  integration_raw_call_requests target =
    send_initial_requests ++ [(target,0,[],T,3,2w,4w)]
End
val () = cv_auto_trans integration_raw_call_requests_def;

(* With the oracle, a non-delegate raw_call consumes the next source outcome
   and records its request, as extcall does: a missing or failed outcome
   reverts under revert_on_failure and is returned as BoolV F otherwise, and
   returndata is cut to max_outsize. Address20 is empty. *)
Theorem RawCall_takes_source_oracle:
  integration_raw_call_observe F T 0 20w NONE (INL (Value NoneV))
    NONE send_initial_requests /\
  integration_raw_call_observe F T 0 20w (SOME [])
    (INR (Error (RevertData []))) (SOME 0) (integration_raw_call_requests 20w) /\
  integration_raw_call_observe F T 0 20w
    (SOME [send_outcome F [7w] (2 ** 256)])
    (INR (Error (RevertData [7w]))) (SOME 0)
    (integration_raw_call_requests 20w) /\
  integration_raw_call_observe F F 0 20w
    (SOME [send_outcome F [7w] (2 ** 256)])
    (INL (Value (BoolV F))) (SOME 0) (integration_raw_call_requests 20w) /\
  integration_raw_call_observe F F 1 20w
    (SOME [send_outcome F [7w; 8w] (2 ** 256)])
    (INL (Value (ArrayV (TupleV [BoolV F; BytesV [7w]])))) (SOME 0)
    (integration_raw_call_requests 20w) /\
  integration_raw_call_observe F T 1 20w
    (SOME [send_outcome T [5w; 6w] 17; send_outcome F [] 0])
    (INL (Value (BytesV [5w]))) (SOME 1)
    (integration_raw_call_requests 20w) /\
  integration_raw_call_observe F T 0 9w (SOME [send_outcome T [] 17])
    (INL (Value NoneV)) (SOME 0) (integration_raw_call_requests 9w)
Proof
  CONV_TAC cv_eval
QED

(* The fixture above makes every non-delegate call static, so adopt_call_outcome
   leaves the state alone.  A plain raw_call(target, data) is a CALL with value
   0: a successful outcome's accounts, transient storage and logs are adopted,
   and a failed one changes nothing but the request and outcome lists. *)
Definition integration_raw_call_adopt_observe_def:
  integration_raw_call_adopt_observe rof outsize target os expected
      balance nonce code persistent transient logs rqs rest =
    let e = Call NoneT (RawCallTarget
      <|rcf_is_static := F; rcf_is_delegate := F;
        rcf_revert_on_failure := rof; rcf_max_outsize := outsize;
        rcf_kws := []|>)
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [target]));
       Literal (BaseT (BytesT (Dynamic 1))) (BytesL [])] NONE in
    let r = cpscv_run e (send_state with outcomes := os) in
      FST r = expected /\
      send_snapshot balance nonce code persistent transient logs rqs rest (SND r)
End
val () = cv_auto_trans integration_raw_call_adopt_observe_def;

Theorem RawCall_call_adopts_source_oracle:
  integration_raw_call_adopt_observe T 1 20w
    (SOME [send_outcome T [5w; 6w] 17; cpscv_tail])
    (INL (Value (BytesV [5w]))) 17 5 [0w] 9w 8w cpscv_adopted_logs
    (send_requests 20w 0) cpscv_tail_snapshot /\
  integration_raw_call_adopt_observe F 0 20w
    (SOME [send_outcome F [7w] (2 ** 256); cpscv_tail])
    (INL (Value (BoolV F))) 3 0 [] 2w 4w cpscv_initial_logs
    (send_requests 20w 0) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

(* A computed precompile (here SHA-256 at Address2) is answered without
   consuming an outcome or recording a request, and a delegate raw_call runs
   the callee, ignoring the oracle. *)
Theorem RawCall_precompile_and_delegate_skip_oracle:
  integration_raw_call_observe F F 0 2w (SOME [send_outcome F [] 0])
    (INL (Value (BoolV T))) (SOME 1) send_initial_requests /\
  integration_raw_call_observe T T 0 20w (SOME [send_outcome F [] 0])
    (INL (Value NoneV)) (SOME 1) send_initial_requests
Proof
  CONV_TAC cv_eval
QED

(* The complete rollback equality is certified separately from computable
   snapshots; CV does not decide equality of function-valued account maps. *)
Theorem public_failure_whole_machine_rollback:
  call_external orc gobs integration_machine tx = (INR exc,am,rqs) ==>
  am = integration_machine
Proof
  metis_tac[call_external_error_rollback]
QED
