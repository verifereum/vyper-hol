(* Local actual-helper/CV checks; no evaluator activation or fixture semantics.
   Inline monadic tails below are the parameterized contracts' actual clients. *)
Theory vyperCallOutcomeTest
Ancestors
  arithmetic list option pair sum words
  vfmState vfmTypes extCallOracle vyperRuntimeAccounts
  vyperAST vyperValue vyperState vyperCallOutcome vyperCallOutcomeBranches
Libs cv_transLib wordsLib monadsyntax

Definition outcome_test_state_def:
  outcome_test_state = empty_state with
    <|accounts := update_account 11w (empty_account_state with balance := 3) empty_accounts;
      tStorage := update_transient_storage 11w
        (update_storage 1w 4w empty_storage) empty_transient_storage;
      logs := [<|logger := 11w; topics := []; data := [3w]|>];
      requests := [call_outcome_request 12w [] (SOME 0) empty_state]|>
End
val () = cv_auto_trans outcome_test_state_def;

Definition outcome_test_outcome_def:
  outcome_test_outcome success balance =
    <|co_success := success; co_returnData := [42w];
      co_accounts := update_account 11w (empty_account_state with balance := balance) empty_accounts;
      co_tStorage := update_transient_storage 11w
        (update_storage 1w 8w empty_storage) empty_transient_storage;
      co_logs := [<|logger := 11w; topics := [1w]; data := [8w]|>]|>
End
val () = cv_auto_trans outcome_test_outcome_def;

(* Numeric observations avoid equality on function-containing record values.
   Whole-record equations are independently proved in the helper owner. *)
Definition outcome_test_snapshot_def:
  outcome_test_snapshot balance slot logs requests remaining st <=>
    (lookup_account 11w st.accounts).balance = balance /\
    lookup_storage 1w (lookup_transient_storage 11w st.tStorage) = slot /\
    LENGTH st.logs = logs /\ LENGTH st.requests = requests /\
    (case st.outcomes of NONE => F | SOME os => LENGTH os = remaining)
End
val () = cv_auto_trans outcome_test_snapshot_def;

Definition outcome_test_take_adopt_def:
  outcome_test_take_adopt target data value os balance slot logs requests remaining =
    let st = outcome_test_state with outcomes := SOME os in
    case take_call_outcome target data value st of
      (INR _,_) => F
    | (INL (rq,outcome),st1) =>
        rq.cr_target = target /\ rq.cr_data = data /\
        (lookup_account 11w rq.cr_accounts).balance = 3 /\
        lookup_storage 1w (lookup_transient_storage 11w rq.cr_tStorage) = 4w /\
        outcome_test_snapshot balance slot logs requests remaining
          (SND (adopt_call_outcome rq outcome st1))
End
val () = cv_auto_trans outcome_test_take_adopt_def;

Theorem outcome_ordinary_success_cv:
  outcome_test_take_adopt 9w [1w] (SOME 5)
    [outcome_test_outcome T 17; outcome_test_outcome F 0] 17 8w 2 2 1 /\
  outcome_test_take_adopt 2w [] (SOME 1)
    [outcome_test_outcome T 17] 17 8w 2 2 0
Proof
  CONV_TAC cv_eval
QED

(* Untyped payloads are intentionally ignored on static/failed outcomes. *)
Theorem outcome_static_failed_cv:
  outcome_test_take_adopt 9w [] NONE
    [outcome_test_outcome T (2 ** 256)] 3 4w 1 2 0 /\
  outcome_test_take_adopt 9w [] (SOME 0)
    [outcome_test_outcome F (2 ** 256)] 3 4w 1 2 0
Proof
  CONV_TAC cv_eval
QED

Theorem outcome_exhausted_computed_cv:
  outcome_test_take_adopt 9w [] (SOME 0) [] 3 4w 1 2 0 /\
  outcome_test_take_adopt 2w [] (SOME 0)
    [outcome_test_outcome F (2 ** 256)] 3 4w 1 1 1 /\
  outcome_test_take_adopt 1w [] NONE [] 3 4w 1 1 0 /\
  outcome_test_take_adopt 6w (REPLICATE 63 0w ++ [1w]) (SOME 0)
    [outcome_test_outcome T 17] 3 4w 1 1 1
Proof
  CONV_TAC cv_eval
QED

Definition outcome_test_error_observations_def:
  outcome_test_error_observations = (
    (case take_call_outcome 9w [] (SOME 0) outcome_test_state of
       (INR exc,st) => exc = Error (RuntimeError "take_call_outcome") /\
         IS_NONE st.outcomes /\ LENGTH st.requests = 1
     | _ => F) /\
    (case take_call_outcome 9w [] (SOME 0)
       (outcome_test_state with outcomes :=
         SOME [outcome_test_outcome T (2 ** 256); outcome_test_outcome T 17]) of
       (INR exc,st) => exc = Error (RuntimeError "call outcome accounts") /\
         outcome_test_snapshot 3 4w 1 2 1 st
     | _ => F) /\
    (case take_call_outcome 2w [] (SOME 0)
       (outcome_test_state with
         <|accounts := (outcome_test_outcome T (2 ** 256)).co_accounts;
           outcomes := SOME [outcome_test_outcome T 17]|>) of
       (INR exc,st) => exc = Error (RuntimeError "call outcome accounts") /\
         outcome_test_snapshot (2 ** 256) 4w 1 1 1 st
     | _ => F))
End
val () = cv_auto_trans outcome_test_error_observations_def;

Theorem outcome_guard_rejected_NONE_cv:
  outcome_test_error_observations
Proof
  CONV_TAC cv_eval
QED

(* These are the real Send/ExtCall monadic tails, translated after ordinary
   monad elimination. The continuation returns the bytes in this small client;
   it is not a new evaluator, decoder, or alternative oracle API. *)
Definition outcome_test_branch_observations_def:
  outcome_test_branch_observations =
    let st = outcome_test_state with outcomes := SOME [] in
    let sent = (do
      (rq,outcome) <- take_call_outcome 9w [] (SOME 0);
      check outcome.co_success "send failed";
      adopt_call_outcome rq outcome;
      return (Value NoneV)
    od) st in
    FST sent = INR (Error (RuntimeError "send failed")) /\
    outcome_test_snapshot 3 4w 1 2 0 (SND sent) /\
    let st = outcome_test_state with outcomes := SOME [outcome_test_outcome T 17] in
    let stopped = (do
      accounts <- get_accounts;
      check (~NULL (lookup_account 9w accounts).code) "ExtCall target has no code";
      (rq,outcome) <- take_call_outcome 9w [] (SOME 0);
      check outcome.co_success "ExtCall reverted";
      adopt_call_outcome rq outcome;
      return (Value (BytesV outcome.co_returnData))
    od) st in
    FST stopped = INR (Error (RuntimeError "ExtCall target has no code")) /\
    outcome_test_snapshot 3 4w 1 1 1 (SND stopped) /\
    let sent_ok = (do
      (rq,outcome) <- take_call_outcome 9w [] (SOME 0);
      check outcome.co_success "send failed";
      adopt_call_outcome rq outcome;
      return (Value NoneV)
    od) st in
    FST sent_ok = INL (Value NoneV) /\
    outcome_test_snapshot 17 8w 2 2 0 (SND sent_ok) /\
    let continued = (do
      (rq,outcome) <- take_call_outcome 9w [] (SOME 0);
      check outcome.co_success "ExtCall reverted";
      adopt_call_outcome rq outcome;
      return (Value (BytesV outcome.co_returnData))
    od) st in
    FST continued = INL (Value (BytesV [42w])) /\
    outcome_test_snapshot 17 8w 2 2 0 (SND continued)
End
val () = outcome_test_branch_observations_def
  |> SRULE [bind_def, ignore_bind_def, FUN_EQ_THM, pair_CASE_def, UNCURRY,
            sum_CASE_rator, prod_CASE_rator, LET_RATOR, COND_RATOR,
            get_accounts_def, check_def, assert_def, return_def,
            adopt_call_outcome_equation]
  |> cv_auto_trans;

Theorem outcome_branches_cv:
  outcome_test_branch_observations
Proof
  CONV_TAC cv_eval
QED

(* An arbitrary account/storage/log payload still gives exactly shared adoption,
   with the evaluator's typed check already discharged by successful take. *)
Theorem outcome_success_actual_client:
  accounts_runtime_well_typed st.accounts /\
  take_call_outcome target calldata value st = (INL (rq,outcome),st1) /\
  adopt_call_outcome rq outcome st1 = (INL (),st2) ==>
  accounts_runtime_well_typed st2.accounts /\
  rq.cr_accounts = st.accounts /\ rq.cr_tStorage = st.tStorage /\
  st2 = st with <|accounts := st2.accounts; tStorage := st2.tStorage;
                 logs := st2.logs; outcomes := st2.outcomes;
                 requests := st2.requests|>
Proof
  rpt strip_tac
  >- (drule_all take_adopt_call_outcome_typed >> simp[]) >>
  drule_all checked_call_outcome_success_frame >> simp[]
QED
