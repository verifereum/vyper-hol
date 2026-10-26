(* Direct source CPS/CV regressions for activated ExtCall.  Numeric snapshots
   avoid comparing function-valued accounts/storage; the original whole-result
   consumption gate remains in vyperExtCallCpsEquivalenceTest.  No big-step rewrites here. *)
Theory vyperExtCallCpsCVTest
Ancestors
  vyperSmallStep[ignore_grammar] extCallOracle
  vyperCallOutcome[ignore_grammar] vfmState[ignore_grammar]
  vfmExecution[ignore_grammar] vfmContext[ignore_grammar]
  vyperState vyperContext vyperABI vyperAST vyperValue
  list option pair finite_map words vfmTypes
Libs cv_transLib wordsLib

Definition cpscv_run_def:
  cpscv_run e st = vyperSmallStep$fromtvk (vyperSmallStep$cont
    (vyperSmallStep$eval_expr_cps empty_evaluation_context e st vyperSmallStep$DoneK))
End
val () = cv_auto_trans cpscv_run_def;

(* Keyword kinds and operands have matching order: value, then default.
   ExtCall ignores Call's legacy default_ret field. *)
Definition cpscv_call_def:
  cpscv_call static target ret dflt = Call ret
    (ExtCall static F ("f",[],ret)
      ((if static then [] else [EKValue]) ++
       (case dflt of NONE => [] | SOME _ => [EKDefault])))
    ([Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [target]))] ++
      (if static then [] else [Literal (BaseT (UintT 256)) (IntL 7)]) ++
      (case dflt of NONE => [] | SOME e => [e])) NONE
End
val () = cv_auto_trans cpscv_call_def;

(* Address 9 remains code-free. Address 13 has code both before and after
   adoption, so successful defaults exercise the post-call code check. *)
Definition cpscv_state_def:
  cpscv_state = empty_state with
    <|accounts := update_account 11w (empty_account_state with balance := 3)
        (update_account 13w (empty_account_state with code := [0w]) empty_accounts);
      tStorage := vfmExecution$update_transient_storage 11w
        (update_storage 1w 4w empty_storage) empty_transient_storage;
      logs := [<|logger := 11w; topics := []; data := [3w]|>];
      scopes := [FEMPTY]; immutables := [(11w,[])];
      requests := [vyperCallOutcome$call_outcome_request 12w [] (SOME 0) empty_state]|>
End
val () = cv_auto_trans cpscv_state_def;

Definition cpscv_outcome_def:
  cpscv_outcome success data balance =
    <|co_success := success; co_returnData := data;
      co_accounts := update_account 11w (empty_account_state with balance := balance)
        (update_account 13w (empty_account_state with code := [0w]) empty_accounts);
      co_tStorage := vfmExecution$update_transient_storage 11w
        (update_storage 1w 8w empty_storage) empty_transient_storage;
      co_logs := [<|logger := 11w; topics := [1w]; data := [8w]|>]; co_toDelete := [] |>
End
val () = cv_auto_trans cpscv_outcome_def;

(* Observe every state field, including incoming request snapshots and the
   remaining outcome payloads.  Balances/storage are projections, not claims
   of universal function equality.  Complete logs and scalar request fields
   are compared, rather than merely their lengths. *)
Definition cpscv_snapshot_def:
  cpscv_snapshot balance slot logs rq_fields remaining st <=>
    (lookup_account 11w st.accounts).balance = balance /\
    (lookup_account 11w st.accounts).nonce = 0 /\
    (lookup_account 11w st.accounts).code = [] /\
    (lookup_account 13w st.accounts).code = [0w] /\
    lookup_storage 1w (lookup_account 11w st.accounts).storage = 0w /\
    lookup_storage 1w (vfmExecution$lookup_transient_storage 11w st.tStorage) = slot /\
    st.logs = logs /\ st.scopes = [FEMPTY] /\ st.immutables = [(11w,[])] /\
    st.pending_deletions = [] /\
    MAP (λrq. (rq.cr_target,rq.cr_value,rq.cr_data,rq.cr_static,
      (lookup_account 11w rq.cr_accounts).balance,
      lookup_storage 1w (vfmExecution$lookup_transient_storage 11w rq.cr_tStorage)))
      st.requests = rq_fields /\
    OPTION_MAP (MAP (λco. (co.co_success,co.co_returnData,
      (lookup_account 11w co.co_accounts).balance,
       lookup_storage 1w (vfmExecution$lookup_transient_storage 11w co.co_tStorage),
       co.co_logs,co.co_toDelete)))
      st.outcomes = remaining
End
val () = cv_auto_trans cpscv_snapshot_def;

Definition cpscv_observe_def:
  cpscv_observe static target ret dflt os expected balance slot logs rqs rest =
    let r = cpscv_run (cpscv_call static target ret dflt)
      (cpscv_state with outcomes := os) in
    FST r = expected /\ cpscv_snapshot balance slot logs rqs rest (SND r)
End
val () = cv_auto_trans cpscv_observe_def;

Definition cpscv_initial_requests_def:
  cpscv_initial_requests = [(12w:address,0:num,[]:word8 list,F,0:num,0w:256 word)]
End
val () = cv_auto_trans cpscv_initial_requests_def;

Definition cpscv_requests_def:
  cpscv_requests static target = cpscv_initial_requests ++
    [(target:address,(if static then 0 else 7),[38w;18w;31w;240w],static,3,4w)]
End
val () = cv_auto_trans cpscv_requests_def;

Definition cpscv_initial_logs_def:
  cpscv_initial_logs = [<|logger := 11w; topics := []; data := [3w]|>]
End
val () = cv_auto_trans cpscv_initial_logs_def;

Definition cpscv_adopted_logs_def:
  cpscv_adopted_logs = cpscv_initial_logs ++ [<|logger := 11w; topics := [1w]; data := [8w]|>]
End
val () = cv_auto_trans cpscv_adopted_logs_def;

Definition cpscv_tail_def:
  cpscv_tail = cpscv_outcome T [99w] 23 with co_toDelete := [31w]
End
val () = cv_auto_trans cpscv_tail_def;

Definition cpscv_tail_snapshot_def:
  cpscv_tail_snapshot = SOME [(T,[99w:word8],23:num,8w:256 word,
    [<|logger := 11w; topics := [1w]; data := [8w]|>],[31w:address])]
End
val () = cv_auto_trans cpscv_tail_snapshot_def;

Theorem cpscv_failed_head_consumed:
  cpscv_observe T 9w (BaseT (UintT 256)) NONE
    (SOME [cpscv_outcome F [] 17; cpscv_tail])
    (INR (Error (RevertData [])))
    3 4w cpscv_initial_logs (cpscv_requests T 9w) cpscv_tail_snapshot /\
  cpscv_observe F 9w (BaseT (UintT 256)) NONE
    (SOME [cpscv_outcome F [] 17; cpscv_tail])
    (INR (Error (RevertData [])))
    3 4w cpscv_initial_logs (cpscv_requests F 9w) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

Theorem cpscv_exhaustion_records_request:
  cpscv_observe T 9w (BaseT (UintT 256)) NONE (SOME [])
    (INR (Error (RevertData [])))
    3 4w cpscv_initial_logs (cpscv_requests T 9w) (SOME []) /\
  cpscv_observe F 9w (BaseT (UintT 256)) NONE (SOME [])
    (INR (Error (RevertData [])))
    3 4w cpscv_initial_logs (cpscv_requests F 9w) (SOME [])
Proof
  CONV_TAC cv_eval
QED

(* NoneT calls perform the no-code check before entering the concrete runner. *)
Theorem cpscv_NONE_concrete_code_failure:
  cpscv_observe T 9w NoneT NONE NONE
    (INR (Error (RuntimeError "ExtCall target has no code")))
    3 4w cpscv_initial_logs cpscv_initial_requests NONE /\
  cpscv_observe F 9w NoneT NONE NONE
    (INR (Error (RuntimeError "ExtCall target has no code")))
    3 4w cpscv_initial_logs cpscv_initial_requests NONE
Proof
  CONV_TAC cv_eval
QED

Theorem cpscv_NoneT_code_failure_before_take:
  cpscv_observe T 9w NoneT NONE (SOME [cpscv_tail])
    (INR (Error (RuntimeError "ExtCall target has no code")))
    3 4w cpscv_initial_logs cpscv_initial_requests cpscv_tail_snapshot /\
  cpscv_observe F 9w NoneT NONE (SOME [cpscv_tail])
    (INR (Error (RuntimeError "ExtCall target has no code")))
    3 4w cpscv_initial_logs cpscv_initial_requests cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

(* ABI uint256 42; empty target code is allowed for SOME value returns.
   Static success ignores even ill-typed account payloads and emitted logs. *)
Theorem cpscv_static_success_decodes_preserves_fields:
  cpscv_observe T 9w (BaseT (UintT 256)) NONE
    (SOME [cpscv_outcome T (REPLICATE 31 0w ++ [42w]) (2 ** 256); cpscv_tail])
    (INL (Value (IntV 42)))
    3 4w cpscv_initial_logs (cpscv_requests T 9w) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

(* The caller has zero balance: SOME does not introduce a source balance
   check.  Request snapshots remain pre-adoption, and logs append in order. *)
Theorem cpscv_nonstatic_success_decodes_adopts_fields:
  cpscv_observe F 9w (BaseT (UintT 256)) NONE
    (SOME [cpscv_outcome T (REPLICATE 31 0w ++ [42w]) 17; cpscv_tail])
    (INL (Value (IntV 42)))
    17 8w cpscv_adopted_logs (cpscv_requests F 9w) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED


(* The entire input outcome queue is unchanged when an operand fails. *)
Definition cpscv_head_snapshot_def:
  cpscv_head_snapshot success data balance = OPTION_MAP
    (CONS (success,data,balance,8w:256 word,
      [<|logger := 11w; topics := [1w]; data := [8w]|>],[]:address list))
    cpscv_tail_snapshot
End
val () = cv_auto_trans cpscv_head_snapshot_def;

(* Empty returndata selects the already evaluated default. The target's
   code survives adoption, so the post-call code check succeeds. *)
Theorem cpscv_empty_return_uses_eager_default:
  cpscv_observe T 13w (BaseT (UintT 256))
    (SOME (Literal (BaseT (UintT 256)) (IntL 77)))
    (SOME [cpscv_outcome T [] 17; cpscv_tail]) (INL (Value (IntV 77)))
    3 4w cpscv_initial_logs (cpscv_requests T 13w) cpscv_tail_snapshot /\
  cpscv_observe F 13w (BaseT (UintT 256))
    (SOME (Literal (BaseT (UintT 256)) (IntL 77)))
    (SOME [cpscv_outcome T [] 17; cpscv_tail]) (INL (Value (IntV 77)))
    17 8w cpscv_adopted_logs (cpscv_requests F 13w) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

(* A valid eager default does not bypass the post-call code check. Failure
   here is after consumption and, for nonstatic calls, after adoption. *)
Theorem cpscv_empty_return_default_checks_code_after_call:
  cpscv_observe T 9w (BaseT (UintT 256))
    (SOME (Literal (BaseT (UintT 256)) (IntL 77)))
    (SOME [cpscv_outcome T [] 17; cpscv_tail])
    (INR (Error (RuntimeError "ExtCall target has no code")))
    3 4w cpscv_initial_logs (cpscv_requests T 9w) cpscv_tail_snapshot /\
  cpscv_observe F 9w (BaseT (UintT 256))
    (SOME (Literal (BaseT (UintT 256)) (IntL 77)))
    (SOME [cpscv_outcome T [] 17; cpscv_tail])
    (INR (Error (RuntimeError "ExtCall target has no code")))
    17 8w cpscv_adopted_logs (cpscv_requests F 9w) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

(* Even with nonempty returndata queued, a failing default stops evaluation
   before a request is recorded or any outcome is consumed. *)
Theorem cpscv_nonempty_return_default_error_before_call:
  cpscv_observe T 9w (BaseT (UintT 256)) (SOME (Name (BaseT (UintT 256)) "missing"))
    (SOME [cpscv_outcome T (REPLICATE 31 0w ++ [42w]) 17; cpscv_tail])
    (INR (Error (TypeError "Name not in scope")))
    3 4w cpscv_initial_logs cpscv_initial_requests
      (cpscv_head_snapshot T (REPLICATE 31 0w ++ [42w]) 17) /\
  cpscv_observe F 9w (BaseT (UintT 256)) (SOME (Name (BaseT (UintT 256)) "missing"))
    (SOME [cpscv_outcome T (REPLICATE 31 0w ++ [42w]) 17; cpscv_tail])
    (INR (Error (TypeError "Name not in scope")))
    3 4w cpscv_initial_logs cpscv_initial_requests
      (cpscv_head_snapshot T (REPLICATE 31 0w ++ [42w]) 17)
Proof
  CONV_TAC cv_eval
QED

(* The default reads a pre-call snapshot: both return 3, even though the
   nonstatic call subsequently adopts balance 17, storage 8 and new logs. *)
Theorem cpscv_default_observes_pre_adoption_state:
  cpscv_observe T 13w (BaseT (UintT 256))
    (SOME (Builtin (BaseT (UintT 256)) (Acc Balance)
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [11w]))]))
    (SOME [cpscv_outcome T [] 17; cpscv_tail]) (INL (Value (IntV 3)))
    3 4w cpscv_initial_logs (cpscv_requests T 13w) cpscv_tail_snapshot /\
  cpscv_observe F 13w (BaseT (UintT 256))
    (SOME (Builtin (BaseT (UintT 256)) (Acc Balance)
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [11w]))]))
    (SOME [cpscv_outcome T [] 17; cpscv_tail]) (INL (Value (IntV 3)))
    17 8w cpscv_adopted_logs (cpscv_requests F 13w) cpscv_tail_snapshot
Proof
  CONV_TAC cv_eval
QED

(* An operand error also precedes a queued revert: the failing outcome and
   tail remain available, and all incoming state projections are retained. *)
Theorem cpscv_failed_outcome_default_error_before_call:
  cpscv_observe T 9w (BaseT (UintT 256)) (SOME (Name (BaseT (UintT 256)) "missing"))
    (SOME [cpscv_outcome F [] 17; cpscv_tail])
    (INR (Error (TypeError "Name not in scope")))
    3 4w cpscv_initial_logs cpscv_initial_requests
      (cpscv_head_snapshot F [] 17) /\
  cpscv_observe F 9w (BaseT (UintT 256)) (SOME (Name (BaseT (UintT 256)) "missing"))
    (SOME [cpscv_outcome F [] 17; cpscv_tail])
    (INR (Error (TypeError "Name not in scope")))
    3 4w cpscv_initial_logs cpscv_initial_requests
      (cpscv_head_snapshot F [] 17)
Proof
  CONV_TAC cv_eval
QED

Definition cpscv_computed_observations_def:
  cpscv_computed_observations =
    let r = cpscv_run (cpscv_call T 2w (BaseT (UintT 256)) NONE)
      (cpscv_state with outcomes := SOME [cpscv_tail]) in
    FST r = INL (Value (IntV
      76608535402990681306785640849444230170906828356424760867673094225215694626710)) /\
    cpscv_snapshot 3 4w cpscv_initial_logs
      cpscv_initial_requests cpscv_tail_snapshot (SND r) /\
    let nr = cpscv_run
      (Call (BaseT (UintT 256)) (ExtCall F F ("f",[],BaseT (UintT 256)) [EKValue])
        [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [2w]));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE)
      (cpscv_state with outcomes := SOME [cpscv_tail]) in
    FST nr = FST r /\ cpscv_snapshot 3 4w cpscv_initial_logs
      cpscv_initial_requests cpscv_tail_snapshot (SND nr)
End
val () = cv_auto_trans cpscv_computed_observations_def;

Theorem cpscv_computed_no_consumption_no_request:
  cpscv_computed_observations
Proof
  CONV_TAC cv_eval
QED
