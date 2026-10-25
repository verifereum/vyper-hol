(* Big-step Send checks, independently unfolding the activated clause.
   CPS equations above are executed directly by CV, not substituted here. *)
Theory vyperSendModesTest
Ancestors
  vyperSendCpsCVTest vyperExtCallCpsCVTest vyperInterpreter vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperState vyperContext vyperABI vyperAST vyperValue
  vyperValueOperation list option pair finite_map words vfmTypes
  vfmState[ignore_grammar] vfmExecution[ignore_grammar]
Libs cv_transLib wordsLib

val send_monad_simps = [vyperStateTheory.bind_def,
  vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
  vyperStateTheory.raise_def, vyperStateTheory.type_check_def,
  vyperStateTheory.check_def, vyperStateTheory.assert_def,
  vyperStateTheory.lift_option_type_def, vyperStateTheory.get_Value_def];

(* Independent NONE-mode tail: run the recipient with send's default zero
   forwarded gas, reject a failed call, then adopt its accounts/storage/logs.
   In particular this is not the old transfer_value-only approximation. *)
Definition send_concrete_backend_def:
  send_concrete_backend target amount = do
    accounts <- get_accounts;
    tStorage <- get_transient_storage;
    result <- lift_option
      (run_ext_call empty_evaluation_context.txn.target target [] (SOME amount)
                    0 accounts tStorage
                    (vyper_to_tx_params empty_evaluation_context.txn))
      "send run failed";
    success <<- FST result; result1 <<- SND result;
    result2 <<- SND result1;
    accounts' <<- FST result2; result3 <<- SND result2;
    tStorage' <<- FST result3; emitted_logs <<- SND result3;
    check success "send failed";
    update_accounts (K accounts');
    update_transient (K tStorage');
    append_logs emitted_logs;
    return (Value NoneV)
  od
End

Theorem send_address_literal:
  (word_of_bytes_be (REPLICATE 19 0w ++ [9w]) : address) = 9w
Proof
  CONV_TAC cv_eval
QED

Theorem send_bigstep_after_arguments:
  eval_expr empty_evaluation_context (send_call 9w 7) st =
    (case st.outcomes of
     | NONE => send_concrete_backend 9w 7
     | SOME _ => do
         (rq,co) <- take_call_outcome 9w [] (SOME 7);
         check co.co_success "send failed";
         adopt_call_outcome rq co;
         return (Value NoneV)
       od) st
Proof
  Cases_on `st.outcomes` >>
  simp (send_monad_simps @ [send_call_def, evaluate_def,
       evaluate_literal_def, dest_AddressV_def,
       dest_NumV_def, vyperStateTheory.materialise_def, send_address_literal,
       eval_send_def, ext_call_kwarg_def, forwarded_gas_def,
       send_concrete_backend_def])
QED

Theorem send_zero_address_literal:
  (word_of_bytes_be (REPLICATE 20 0w) : address) = 0w /\
  (word_of_bytes_be (REPLICATE 19 0w ++ [0w]) : address) = 0w
Proof
  CONV_TAC cv_eval
QED

Theorem send_zero_bigstep_after_arguments:
  eval_expr empty_evaluation_context (send_call 0w 0) st =
    (case st.outcomes of
     | NONE => send_concrete_backend 0w 0
     | SOME _ => do
         (rq,co) <- take_call_outcome 0w [] (SOME 0);
         check co.co_success "send failed";
         adopt_call_outcome rq co;
         return (Value NoneV)
       od) st
Proof
  Cases_on `st.outcomes` >>
  simp (send_monad_simps @ [send_call_def, evaluate_def,
       evaluate_literal_def, dest_AddressV_def, dest_NumV_def,
       vyperStateTheory.materialise_def, send_zero_address_literal,
       eval_send_def, ext_call_kwarg_def, forwarded_gas_def,
       send_concrete_backend_def])
QED

(* Closed actual counterexample to the old inert-mode Send conjunct, saved
   before amending it: ordinary zero-value Send still records/exhausts. *)
Theorem send_zero_initial_state_not_inert:
  let st = initial_state initial_machine_state [FEMPTY] with outcomes := SOME [] in
    eval_expr empty_evaluation_context (send_call 0w 0) st =
      (INR (Error (RuntimeError "send failed")),
       st with requests := [call_outcome_request 0w [] (SOME 0) st]) /\
    eval_expr empty_evaluation_context (send_call 0w 0) st <> (INL (Value NoneV),st)
Proof
  simp (send_monad_simps @ [send_zero_bigstep_after_arguments, initial_state_def,
       take_call_outcome_def, call_outcome_request_def, take_outcome_def,
       record_request_def, computed_precompile_addresses, failed_outcome_def,
       empty_state_def, UNCURRY])
QED

Theorem send_bigstep_failure_whole_state:
  eval_expr empty_evaluation_context (send_call 9w 7)
    (send_state with outcomes := SOME [send_outcome F [] (2 ** 256); cpscv_tail]) =
    (INR (Error (RuntimeError "send failed")),
     send_state with <|outcomes := SOME [cpscv_tail];
       requests := send_state.requests ++
         [call_outcome_request 9w [] (SOME 7) send_state]|>)
Proof
  simp (send_monad_simps @ [send_bigstep_after_arguments, take_call_outcome_def,
       call_outcome_request_def, take_outcome_def, record_request_def,
       computed_precompile_addresses, send_outcome_def, cpscv_outcome_def,
       send_state_def, cpscv_state_def, empty_state_def, UNCURRY])
QED

Theorem send_success_payload_account_guard:
  accounts_runtime_well_typed (send_outcome T [99w] 17).co_accounts
Proof
  CONV_TAC cv_eval
QED

Theorem send_bigstep_success_whole_state:
  eval_expr empty_evaluation_context (send_call 9w 7)
    (send_state with outcomes := SOME [send_outcome T [99w] 17; cpscv_tail]) =
    (INL (Value NoneV), send_state with
      <|accounts := (send_outcome T [99w] 17).co_accounts;
        tStorage := (send_outcome T [99w] 17).co_tStorage;
        logs := send_state.logs ++ (send_outcome T [99w] 17).co_logs;
        pending_deletions := (send_outcome T [99w] 17).co_toDelete;
        outcomes := SOME [cpscv_tail];
        requests := send_state.requests ++
          [call_outcome_request 9w [] (SOME 7) send_state]|>)
Proof
  simp (send_monad_simps @ [send_bigstep_after_arguments, take_call_outcome_def,
       call_outcome_request_def, take_outcome_def, record_request_def,
       computed_precompile_addresses, send_outcome_def, cpscv_outcome_def,
       send_state_def, cpscv_state_def, empty_state_def, UNCURRY,
       (send_success_payload_account_guard |> SRULE [send_outcome_def, cpscv_outcome_def]),
       adopt_call_outcome_def, adopt_outcome_def, adopt_outcome_deletions_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       vyperStateTheory.append_logs_def,
       empty_account_state_def])
QED
