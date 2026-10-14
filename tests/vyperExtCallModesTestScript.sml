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
   assert_def, raise_def, lift_option_type_def, lift_sum_runtime_def,
   lookup_account_def, empty_accounts_def, empty_account_state_def,
   evaluate_literal_def, dest_AddressV_def, get_Value_def, materialise_def,
   empty_evaluation_context_def, get_tenv_def, get_accounts_def,
   take_call_outcome_def, call_outcome_request_def, take_outcome_def,
   record_request_def, computed_precompile_addresses, failed_outcome_def,
   empty_state_def, UNCURRY, sum_CASE_rator, option_CASE_rator];

Theorem activated_NONE_keeps_concrete_code_check:
  eval_expr empty_evaluation_context counter_expr empty_state =
    (INR (Error (RuntimeError "ExtCall target has no code")),empty_state)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Theorem activated_exhaustion_records_request:
  eval_expr empty_evaluation_context counter_expr
    (empty_state with outcomes := SOME []) =
    (INR (Error (RuntimeError "ExtCall reverted")),
     empty_state with <|outcomes := SOME []; requests := [counter_request]|>)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Theorem activated_NoneT_checks_code_before_take:
  eval_expr empty_evaluation_context
    (Call NoneT (ExtCall T F ("f",[],NoneT))
      [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]))] NONE)
    counter_state =
    (INR (Error (RuntimeError "ExtCall target has no code")),counter_state)
Proof
  simp EXT_CALL_FIXTURE_SIMP >> CONV_TAC cv_eval
QED

Definition sha256_expr_def:
  sha256_expr = Call (BaseT (UintT 256))
    (ExtCall T F ("f",[],BaseT (UintT 256)))
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
