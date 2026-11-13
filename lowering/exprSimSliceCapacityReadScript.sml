(* Capacity at capture exit uses only the final length read. *)
Theory exprSimSliceCapacityRead
Ancestors
  exprSimSliceSource vyperInterpreter vyperState vyperValueOperation
  vyperTypeSystem vyperTypeExprSoundness vyperTyping

Theorem slice_literal_read_length:
  bind (eval_expr cx (Literal lt (IntL j))) (read_result cx) es =
    (INL (IntV (&k)),ee) ==> j = &k
Proof
  simp[evaluate_def, bind_def, ignore_bind_def, return_def,
       lift_sum_def, read_result_def, evaluate_literal_def, AllCaseEqs()]
QED

Theorem slice_read_capacity:
  slice_operands_ok (Slice n) [src;start;len] /\
  bind (eval_expr cx len) (read_result cx) es = (INL (IntV (&k)),ee) /\
  L <= bytelike_type_bound (expr_type src) /\ i+k <= L ==> k <= n
Proof
  strip_tac >> drule slice_capacity_alternatives >> strip_tac
  >- (gvs[] >> drule slice_literal_read_length >> intLib.ARITH_TAC) >>
  decide_tac
QED

Theorem slice_captured_bytes_length:
  value_runtime_typed env (BaseT (BytesT bd)) (BytesV bs) ==>
  LENGTH bs <= bytelike_type_bound (BaseT (BytesT bd))
Proof
  Cases_on `bd` >>
  simp[value_runtime_typed_def, vyperValueTheory.evaluate_type_def, value_has_type_def,
       bytelike_type_bound_def]
QED

Theorem slice_captured_string_length:
  value_runtime_typed env (BaseT (StringT m)) (StringV bs) ==>
  LENGTH bs <= bytelike_type_bound (BaseT (StringT m))
Proof
  simp[value_runtime_typed_def, vyperValueTheory.evaluate_type_def, value_has_type_def,
       bytelike_type_bound_def]
QED
