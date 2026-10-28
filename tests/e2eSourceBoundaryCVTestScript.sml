(* Actual SOURCE entry calls, not inert helper or CPS-equivalence substitutes.
   Uses accepted Source034's oracle argument and triple result. No source,
   compiler or fixture definition is changed. *)
Theory e2eSourceBoundaryCVTest
Ancestors
  vyperSendCpsCVTest vyperExtCallCpsCVTest vyperSmallStep[ignore_grammar]
  vyperInterpreter vyperState vyperContext vyperAST vyperValue
  extCallOracle selectorDispatch
  vfmState[ignore_grammar] vfmExecution[ignore_grammar]
  words list option pair finite_map
Libs cv_transLib wordsLib

Definition boundary_source_program_def:
  boundary_source_program =
    [FunctionDecl External Payable F F "send" [] [] NoneT [Expr (send_call 9w 1)];
     FunctionDecl External Payable F F "ext" [] [] NoneT
       [Expr (Call NoneT (ExtCall F F ("ping",[],NoneT))
         [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]));
          Literal (BaseT (UintT 256)) (IntL 1)] NONE)]]
End
val () = cv_auto_trans boundary_source_program_def;

Definition boundary_source_machine_def:
  boundary_source_machine = initial_machine_state with
    <|sources := [(0w,[(NONE,boundary_source_program)])];
      accounts := update_account 8w (empty_account_state with balance := 5)
        (update_account 0w (empty_account_state with balance := 2)
          (update_account 9w (empty_account_state with code := [0w]) empty_accounts))|>
End
val () = cv_auto_trans boundary_source_machine_def;

Definition boundary_source_tx_def:
  boundary_source_tx name = empty_call_txn with
    <|function_name := name; sender := 8w; target := 0w; value := 1|>
End
val () = cv_auto_trans boundary_source_tx_def;

(* Source entry has transferred 1 before recording either body request.
   Observe both source accounts and transient snapshot; no leftover outcome
   comparison is smuggled into the request observation. *)
Definition boundary_source_requests_def:
  boundary_source_requests rqs = MAP (λrq.
    (rq.cr_target,rq.cr_value,rq.cr_data,rq.cr_static,
     (lookup_account 0w rq.cr_accounts).balance,
     (lookup_account 8w rq.cr_accounts).balance,
     lookup_storage 1w (vfmExecution$lookup_transient_storage 11w rq.cr_tStorage))) rqs
End
val () = cv_auto_trans boundary_source_requests_def;

Definition boundary_source_some_success_def:
  boundary_source_some_success name data =
    let (res,am,rqs) = call_external (SOME [send_outcome T [] 17;cpscv_tail]) []
      boundary_source_machine (boundary_source_tx name) in
      res = INL NoneV /\
      (lookup_account 11w am.accounts).balance = 17 /\
      (lookup_account 11w am.accounts).nonce = 5 /\
      (lookup_account 11w am.accounts).code = [0w] /\
      lookup_storage 1w (lookup_account 11w am.accounts).storage = 9w /\
      lookup_storage 1w (vfmExecution$lookup_transient_storage 11w am.tStorage) = 8w /\
      am.logs = [<|logger := 11w; topics := [1w]; data := [8w]|>] /\
      boundary_source_requests rqs = [(9w,1,data,F,3,4,0w)]
End
val () = cv_auto_trans boundary_source_some_success_def;

Theorem root_SOME_Send_and_ExtCall_adopt_and_record_posttransfer:
  boundary_source_some_success "send" [] /\
  boundary_source_some_success "ext" (function_selector "ping" [])
Proof
  CONV_TAC cv_eval
QED

Definition boundary_source_some_failure_def:
  boundary_source_some_failure name data message os =
    let (res,am,rqs) = call_external (SOME os) []
      boundary_source_machine (boundary_source_tx name) in
      res = INR (Error (RuntimeError message)) /\
      (lookup_account 0w am.accounts).balance = 2 /\
      (lookup_account 8w am.accounts).balance = 5 /\
      (lookup_account 11w am.accounts).balance = 0 /\ am.logs = [] /\
      boundary_source_requests rqs = [(9w,1,data,F,3,4,0w)]
End
val () = cv_auto_trans boundary_source_some_failure_def;

Theorem root_SOME_failure_and_exhaustion_keep_requests_roll_back_machine:
  boundary_source_some_failure "send" [] "send failed" [send_outcome F [] 17;cpscv_tail] /\
  boundary_source_some_failure "send" [] "send failed" [] /\
  boundary_source_some_failure "ext" (function_selector "ping" []) "ExtCall reverted"
    [send_outcome F [] 17;cpscv_tail] /\
  boundary_source_some_failure "ext" (function_selector "ping" []) "ExtCall reverted" []
Proof
  CONV_TAC cv_eval
QED

Definition boundary_source_none_def:
  boundary_source_none =
    let (res,am,rqs) = call_external NONE [] boundary_source_machine (boundary_source_tx "send") in
      res = INL NoneV /\
      (lookup_account 0w am.accounts).balance = 2 /\
      (lookup_account 8w am.accounts).balance = 4 /\
      (lookup_account 9w am.accounts).balance = 1 /\
      (lookup_account 11w am.accounts).balance = 0 /\
      am.logs = [] /\ rqs = []
End
val () = cv_auto_trans boundary_source_none_def;

Theorem root_NONE_Send_is_still_concrete:
  boundary_source_none
Proof
  CONV_TAC cv_eval
QED
