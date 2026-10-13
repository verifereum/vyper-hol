(* Independent activated-evaluator witness; no preservation theorem is an ancestor. *)
Theory vyperExtCallConsumptionTest
Ancestors
  vyperCallOutcome extCallOracle
  vyperInterpreter vyperState vyperContext vyperABI vyperAST vyperValue
  vyperValueOperation list finite_map words vfmTypes pair
Libs wordsLib cv_transLib

Definition counter_expr_def:
  counter_expr = Call (BaseT (UintT 256))
    (ExtCall T ("f", [], BaseT (UintT 256)))
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [9w]))] NONE
End

Definition counter_outcome_def:
  counter_outcome = failed_outcome (call_outcome_request 9w [] NONE empty_state)
End

Definition counter_state_def:
  counter_state = empty_state with outcomes := SOME [counter_outcome]
End

Definition counter_request_def:
  counter_request = call_outcome_request 9w
    (THE (build_ext_calldata FEMPTY "f" [] [])) NONE empty_state
End

Theorem counter_address:
  (word_of_bytes_be (REPLICATE 19 0w ++ [9w]) : address) = 9w
Proof
  CONV_TAC cv_eval
QED

Theorem counter_calldata:
  build_ext_calldata FEMPTY "f" [] [] = SOME [38w;18w;31w;240w]
Proof
  CONV_TAC cv_eval
QED

Theorem activated_ExtCall_consumes_counterexample:
  eval_expr empty_evaluation_context counter_expr counter_state =
    (INR (Error (RuntimeError "ExtCall reverted")),
     counter_state with <|outcomes := SOME []; requests := [counter_request]|>) /\
  (SND (eval_expr empty_evaluation_context counter_expr counter_state)).outcomes <>
    counter_state.outcomes /\
  (SND (eval_expr empty_evaluation_context counter_expr counter_state)).requests =
    [counter_request]
Proof
  simp[counter_expr_def, counter_state_def, counter_outcome_def,
       counter_request_def, counter_calldata, counter_address, evaluate_def,
       bind_def, ignore_bind_def, return_def, type_check_def, check_def,
       assert_def, raise_def, lift_option_type_def,
       evaluate_literal_def, dest_AddressV_def, get_Value_def, materialise_def,
       empty_evaluation_context_def, get_tenv_def,
       get_accounts_def, take_call_outcome_def, call_outcome_request_def,
       take_outcome_def, record_request_def, computed_precompile_addresses,
       failed_outcome_def, empty_state_def, UNCURRY]
QED
