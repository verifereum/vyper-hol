(* Semantic diagnostic only: this is not a counterexample to target_walk_frame. *)
Theory targetPureWalkProbe
Ancestors
  exprLowering vyperMachineFrame vyperInterpreter vyperContext vyperState
  vyperValue vyperValueOperation

Theorem raw_log_classified_nonmutating:
  ~expr_can_mutate cenv
    (Call NoneT RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 0))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic 0)) [];
       Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])] NONE)
Proof
  simp[expr_can_mutate_def, call_can_mutate_def]
QED

Theorem raw_log_empty_execution:
  ~cx.txn.is_static ==>
  eval_expr cx
    (Call NoneT RawLog
      [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 0))
        (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic 0)) [];
       Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])] NONE) s =
  (INL (Value NoneV),
   s with logs := s.logs ++ [encode_raw_event_values cx.txn.target [] []])
Proof
  strip_tac >>
  simp[evaluate_def, builtin_args_length_ok_def, compatible_bound_def,
       evaluate_builtin_def, evaluate_type_def, make_array_value_def,
       evaluate_literal_def, read_result_def, dest_ArrayV_def, dest_BytesV_def,
       check_not_static_def, push_log_def, get_accounts_def,
       precompile_call_success_def, lift_sum_def, lift_option_type_def,
       type_check_def, check_def, assert_def, ignore_bind_def, bind_def,
       return_def]
QED

Theorem raw_log_empty_not_frame:
  ~machine_frame s
    (s with logs := s.logs ++ [encode_raw_event_values cx.txn.target [] []])
Proof
  simp[machine_frame_def] >>
  strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >>
  simp[]
QED
