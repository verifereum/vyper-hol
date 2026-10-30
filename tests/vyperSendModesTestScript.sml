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
  vyperStateTheory.lift_option_type_def, vyperStateTheory.read_result_def,
  dest_AddressV_def, dest_NumV_def, ext_call_kwarg_def,
  byteTheory.word_of_bytes_be_def,
  (byteTheory.word_of_bytes_word_to_bytes |> INST_TYPE [alpha |-> ``:160``]
    |> SRULE [dividesTheory.compute_divides])];

Theorem send_address_literal:
  (word_of_bytes_be (REPLICATE 19 0w ++ [9w]) : address) = 9w
Proof
  CONV_TAC cv_eval
QED

Theorem send_bigstep_after_arguments:
  eval_expr empty_evaluation_context (send_call 9w 7) st =
    eval_send empty_evaluation_context F [AddressV 9w; IntV 7] st
Proof
  `AddressV 9w = BytesV (REPLICATE 19 0w ++ [9w])` by (CONV_TAC cv_eval) >>
  simp (send_monad_simps @ [send_call_def, evaluate_def, evaluate_literal_def])
QED

Theorem send_zero_address_literal:
  (word_of_bytes_be (REPLICATE 20 0w) : address) = 0w /\
  (word_of_bytes_be (REPLICATE 19 0w ++ [0w]) : address) = 0w
Proof
  CONV_TAC cv_eval
QED

Theorem send_zero_bigstep_after_arguments:
  eval_expr empty_evaluation_context (send_call 0w 0) st =
    eval_send empty_evaluation_context F [AddressV 0w; IntV 0] st
Proof
  `AddressV 0w = BytesV (REPLICATE 19 0w ++ [0w])` by (CONV_TAC cv_eval) >>
  simp (send_monad_simps @ [send_call_def, evaluate_def, evaluate_literal_def])
QED

(* NONE-mode send executes recipient code, even for a zero-value self-send. *)
Theorem send_none_executes_invalid_recipient:
  FST (eval_send empty_evaluation_context F [AddressV 0w; IntV 0]
    (empty_state with accounts := update_account 0w
      (empty_account_state with code := [254w]) empty_accounts)) =
  INR (Error (RuntimeError "send failed"))
Proof
  CONV_TAC cv_eval
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
  simp (send_monad_simps @ [send_zero_bigstep_after_arguments, eval_send_def, initial_state_def,
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
  simp (send_monad_simps @ [send_bigstep_after_arguments, eval_send_def, take_call_outcome_def,
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
        outcomes := SOME [cpscv_tail];
        requests := send_state.requests ++
          [call_outcome_request 9w [] (SOME 7) send_state]|>)
Proof
  simp (send_monad_simps @ [send_bigstep_after_arguments, eval_send_def, take_call_outcome_def,
       call_outcome_request_def, take_outcome_def, record_request_def,
       computed_precompile_addresses, send_outcome_def, cpscv_outcome_def,
       send_state_def, cpscv_state_def, empty_state_def, UNCURRY,
       (send_success_payload_account_guard |> SRULE [send_outcome_def, cpscv_outcome_def]),
       adopt_call_outcome_def, adopt_outcome_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       vyperStateTheory.append_logs_def,
       empty_account_state_def])
QED
