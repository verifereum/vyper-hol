(* Semantic diagnostic only: this is not a counterexample to target_walk_frame. *)
Theory targetPureWalkProbe
Ancestors
  exprLowering vyperMachineFrame vyperInterpreter vyperContext vyperState
  vyperValue vyperValueOperation vyperTypeSystem vyperAST

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

(* A tuple evaluates both fields, then discards the NoneV field. *)
Definition raw_log_index_def:
  raw_log_index =
    Subscript (BaseT (UintT 256))
      (Builtin (TupleT [NoneT; BaseT (UintT 256)])
        (MakeArray NONE (Fixed 2))
        [Call NoneT RawLog
          [Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic 1))
            (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic 1)) [];
           Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])] NONE;
         Literal (BaseT (UintT 256)) (IntL 0)])
      (Literal (BaseT (UintT 256)) (IntL 1))
End

Theorem raw_log_index_nonmutating:
  ~expr_can_mutate cenv raw_log_index
Proof
  simp[raw_log_index_def, expr_can_mutate_def, call_can_mutate_def]
QED

Theorem raw_log_index_typed:
  well_typed_expr env raw_log_index
Proof
  simp[raw_log_index_def, well_typed_expr_def, well_typed_builtin_app_def,
       builtin_operands_ok_def, subscript_type_ok_def,
       subscript_base_type_exact_def, well_formed_type_def, evaluate_type_def,
       well_typed_literal_def, compatible_bound_def, is_int_type_def,
       expr_type_def, type_slot_size_def, bound_length_def, within_int_bound_def,
       wordsTheory.dimword_def] >>
  EVAL_TAC >> simp[venomLayoutTheory.dimindex_256]
QED

Theorem raw_log_index_execution:
  ~cx.txn.is_static ==>
  eval_expr cx raw_log_index s =
    (INL (Value (IntV 0)),
     s with logs := s.logs ++ [encode_raw_event_values cx.txn.target [] []])
Proof
  strip_tac >>
  simp[raw_log_index_def, evaluate_def, builtin_args_length_ok_def,
       compatible_bound_def, evaluate_builtin_def, evaluate_type_def,
       make_array_value_def, evaluate_literal_def, read_result_def,
       dest_ArrayV_def, dest_BytesV_def, check_not_static_def, push_log_def,
       get_accounts_def, precompile_call_success_def, lift_sum_def,
       lift_option_type_def, type_check_def, check_def, assert_def,
       ignore_bind_def, bind_def, return_def,
       expr_type_def, select_result_def, evaluate_subscripts_def,
       type_slot_size_def, wordsTheory.dimword_def,
       venomLayoutTheory.dimindex_256, subscript_type_def, array_index_def,
       listTheory.oEL_def]
QED

Theorem raw_log_target_execution:
  ~cx.txn.is_static /\
  lookup_scopes id s.scopes = SOME entry /\
  entry.type = ArrayTV (BaseTV (UintT 256)) (Dynamic 1) /\
  entry.value = ArrayV (DynArrayV [IntV 7]) ==>
  eval_base_place cx (SubscriptTarget (NameTarget id) raw_log_index) s =
    (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV 0)])),
     s with logs := s.logs ++ [encode_raw_event_values cx.txn.target [] []])
Proof
  strip_tac >>
  simp[Once evaluate_def, Once evaluate_def, get_scopes_def,
       type_check_def, assert_def, ignore_bind_def, bind_def, return_def,
       raw_log_index_execution, read_result_def, extend_place_def,
       place_type_value_def, read_place_def, lift_option_type_def,
       read_memory_path_def, evaluate_subscripts_def, subscripts_type_def,
       subscript_type_def, array_index_def, listTheory.oEL_def,
       extend_memory_place_def, lift_sum_def]
QED
