(* Focused checks against the activated evaluator, independent of preservation. *)
Theory vyperExtCallModesTest
Ancestors
  vyperExtCallConsumptionTest vyperCallOutcome extCallOracle
  vyperInterpreter vyperState vyperContext vyperABI vyperAST vyperValue
  vyperValueOperation list finite_map words vfmTypes pair
  vfmState[ignore_grammar]
Libs wordsLib cv_transLib

val EXT_CALL_FIXTURE_SIMP =
  [counter_expr_def, counter_state_def, counter_outcome_def,
   counter_request_def, counter_calldata, counter_address, evaluate_def,
   bind_def, ignore_bind_def, return_def, type_check_def, check_def,
   assert_def, raise_def, lift_option_type_def, lift_option_def,
   lift_sum_runtime_def, eval_ext_call_def, eval_ext_call_effects_def, ext_call_opts_ok_def,
   ext_call_kwarg_def, ext_call_precheck_ok_def, ext_call_has_code_def,
   lookup_account_def, empty_accounts_def, empty_account_state_def,
   evaluate_literal_def, dest_AddressV_def, get_Value_def, materialise_def,
   empty_evaluation_context_def, get_tenv_def, get_accounts_def,
   take_call_outcome_def, call_outcome_request_def, take_outcome_def,
   record_request_def, computed_precompile_addresses, failed_outcome_def,
   empty_state_def, UNCURRY, sum_CASE_rator, option_CASE_rator];

Theorem activated_NONE_keeps_concrete_code_check:
  eval_expr empty_evaluation_context
    (Call NoneT (ExtCall T F ("f",[],NoneT) [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]))] NONE)
    empty_state =
    (INR (Error (RuntimeError "ExtCall target has no code")),empty_state)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Theorem activated_exhaustion_records_request:
  eval_expr empty_evaluation_context counter_expr
    (empty_state with outcomes := SOME []) =
    (INR (Error (RevertData [])),
     empty_state with <|outcomes := SOME []; requests := [counter_request]|>)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Theorem activated_NoneT_checks_code_before_take:
  eval_expr empty_evaluation_context
    (Call NoneT (ExtCall T F ("f",[],NoneT) [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]))] NONE)
    counter_state =
    (INR (Error (RuntimeError "ExtCall target has no code")),counter_state)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Definition sha256_expr_def:
  sha256_expr = Call (BaseT (UintT 256))
    (ExtCall T F ("f",[],BaseT (UintT 256)) [])
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [2w]))] NONE
End

Theorem sha256_fixture_address:
  (word_of_bytes_be (REPLICATE 19 0w ++ [2w]) : address) = 2w
Proof
  CONV_TAC cv_eval
QED

Theorem activated_precompile_does_not_consume_or_record:
  SND (eval_expr empty_evaluation_context sha256_expr counter_state) = counter_state /\
  ISL (FST (eval_expr empty_evaluation_context sha256_expr counter_state))
Proof
  simp (sha256_expr_def :: sha256_fixture_address :: precompile_result_sha256 ::
        adopt_call_outcome_def :: adopt_outcome_def :: EXT_CALL_FIXTURE_SIMP) >>
  CONV_TAC cv_eval
QED

(* skip_contract_check: the oracle branch makes a void call to a target
   without code instead of reverting before it. *)
Theorem activated_skip_check_makes_call:
  eval_expr empty_evaluation_context
    (Call NoneT (ExtCall T T ("f",[],NoneT) [])
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]))] NONE)
    counter_state =
    (INR (Error (RevertData [])),
     counter_state with <|outcomes := SOME []; requests := [counter_request]|>)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Definition default_expr_def:
  default_expr skip_check default_e = Call (BaseT (UintT 256))
    (ExtCall T skip_check ("f",[],BaseT (UintT 256)) [EKDefault])
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w])); default_e]
    NONE
End

Definition empty_return_state_def:
  empty_return_state = empty_state with outcomes :=
    SOME [counter_outcome with co_success := T]
End

(* On empty return data the default is used only if the target has code,
   unless skip_contract_check. *)
Theorem activated_default_path_checks_code:
  FST (eval_expr empty_evaluation_context
         (default_expr F (Literal (BaseT (UintT 256)) (IntL 7)))
         empty_return_state) =
    INR (Error (RuntimeError "ExtCall target has no code")) /\
  ISL (FST (eval_expr empty_evaluation_context
              (default_expr T (Literal (BaseT (UintT 256)) (IntL 7)))
              empty_return_state))
Proof
  simp (default_expr_def :: empty_return_state_def :: adopt_call_outcome_def ::
        adopt_outcome_def :: EXT_CALL_FIXTURE_SIMP) >>
  CONV_TAC cv_eval
QED

(* The default is evaluated before the call: a failing default stops the
   call from being made. *)
Theorem activated_default_evaluated_before_call:
  ISR (FST (eval_expr empty_evaluation_context
              (default_expr F (Name (BaseT (UintT 256)) "missing"))
              counter_state)) /\
  (SND (eval_expr empty_evaluation_context
          (default_expr F (Name (BaseT (UintT 256)) "missing"))
          counter_state)).requests = []
Proof
  simp (default_expr_def :: EXT_CALL_FIXTURE_SIMP) >> CONV_TAC cv_eval
QED

(* Direct execution forwards gas=: a recipient that stores to a fresh slot
   needs more than the 2300-gas stipend a value transfer adds. The recipient
   is 0x99, since low addresses such as 9 are precompiles. cv_eval runs the
   shared eval_send/eval_ext_call bodies. *)
val DIRECT_CALL_SIMP =
  [evaluate_def, bind_def, ignore_bind_def, return_def, evaluate_literal_def,
   get_Value_def, materialise_def, empty_evaluation_context_def];

Definition sstore_state_def:
  sstore_state = empty_state with accounts :=
    update_account 0x99w
      (empty_account_state with code := [0x60w; 1w; 0x60w; 0w; 0x55w; 0w])
      (update_account 0w (empty_account_state with balance := 10)
         empty_accounts)
End

Definition gas_kwarg_def:
  gas_kwarg gas = case gas of
    | NONE => []
    | SOME g => [Literal (BaseT (UintT 256)) (IntL g)]
End

Definition send_gas_expr_def:
  send_gas_expr gas = Call NoneT (Send (IS_SOME gas))
    ([Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [0x99w]));
      Literal (BaseT (UintT 256)) (IntL 1)] ++ gas_kwarg gas) NONE
End

Definition extcall_gas_expr_def:
  extcall_gas_expr gas = Call NoneT
    (ExtCall F F ("f",[],NoneT) (if IS_SOME gas then [EKGas] else []))
    (Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [0x99w])) ::
     gas_kwarg gas) NONE
End

(* send forwards no gas by default, so the recipient gets only the stipend. *)
Theorem direct_send_forwards_gas:
  FST (eval_expr empty_evaluation_context (send_gas_expr NONE) sstore_state) =
    INR (Error (RuntimeError "send failed")) /\
  FST (eval_expr empty_evaluation_context (send_gas_expr (SOME 2300))
         sstore_state) =
    INR (Error (RuntimeError "send failed")) /\
  FST (eval_expr empty_evaluation_context (send_gas_expr (SOME 50000))
         sstore_state) = INL (Value NoneV)
Proof
  simp (send_gas_expr_def :: gas_kwarg_def :: sstore_state_def ::
        DIRECT_CALL_SIMP) >>
  CONV_TAC cv_eval
QED

(* extcall forwards all gas by default, and only gas= with gas=. *)
Theorem direct_extcall_forwards_gas:
  FST (eval_expr empty_evaluation_context (extcall_gas_expr NONE)
         sstore_state) = INL (Value NoneV) /\
  FST (eval_expr empty_evaluation_context (extcall_gas_expr (SOME 2300))
         sstore_state) =
    INR (Error (RevertData [])) /\
  FST (eval_expr empty_evaluation_context (extcall_gas_expr (SOME 50000))
         sstore_state) = INL (Value NoneV)
Proof
  simp (extcall_gas_expr_def :: gas_kwarg_def :: sstore_state_def ::
        DIRECT_CALL_SIMP) >>
  CONV_TAC cv_eval
QED

(* A recipient that needs 381 gas (LOG0) separates the stipend from the
   forwarded gas: it runs on the stipend alone, which a zero-value call
   does not get. A gas= above the model's limit forwards that limit. *)
Definition log_state_def:
  log_state = empty_state with accounts :=
    update_account 0x99w
      (empty_account_state with code := [0x60w; 0w; 0x60w; 0w; 0xA0w; 0w])
      (update_account 0w (empty_account_state with balance := 10)
         empty_accounts)
End

Definition send_value_expr_def:
  send_value_expr v = Call NoneT (Send F)
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [0x99w]));
     Literal (BaseT (UintT 256)) (IntL v)] NONE
End

Theorem direct_call_stipend_and_cap:
  FST (eval_expr empty_evaluation_context (send_value_expr 1) log_state) =
    INL (Value NoneV) /\
  FST (eval_expr empty_evaluation_context (send_value_expr 0) log_state) =
    INR (Error (RuntimeError "send failed")) /\
  FST (eval_expr empty_evaluation_context
         (extcall_gas_expr (SOME (2 ** 256 - 1))) log_state) =
    INL (Value NoneV)
Proof
  simp (send_value_expr_def :: extcall_gas_expr_def :: gas_kwarg_def ::
        log_state_def :: DIRECT_CALL_SIMP) >>
  CONV_TAC cv_eval
QED
