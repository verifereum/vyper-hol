Theory tuplePlaceChildSize
Ancestors
  placeMemoryChildForward valueEncoding compileEnv context list arithmetic
  vyperLookupStorage

Definition tuple_place_child_size_forward_def:
  tuple_place_child_size_forward cenv tenv ctx func dt <=>
  !st dtv stv v dp sp a b u dw sw.
    type_widens_to tenv st dt /\
    evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
    type_memory_bytes cenv dt = type_memory_size dtv /\
    type_memory_bytes cenv st = type_memory_size stv /\
    value_has_type dtv v /\ val_wf dtv v /\
    value_has_type stv v /\ val_wf stv v /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    type_memory_size dtv + 64 < dimword (:256) /\
    type_memory_size stv + 64 < dimword (:256) /\
    compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
    (!x. dp = Var x ==> not_fresh_at a x) /\
    (!x. sp = Var x ==> not_fresh_at a x) /\
    eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts ==>
    ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
End

Theorem tuple_place_child_size_forward_apply:
  tuple_place_child_size_forward cenv tenv ctx func dt /\
  type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  type_memory_bytes cenv dt = type_memory_size dtv /\
  type_memory_bytes cenv st = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  type_memory_size dtv + 64 < dimword (:256) /\
  type_memory_size stv + 64 < dimword (:256) /\
  compile_store_memory_typed cenv dp dt sp st a = ((),b) /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
Proof
  simp[tuple_place_child_size_forward_def] >> metis_tac[]
QED

Theorem tuple_place_child_interval_bounds:
  B + N < D /\ N + 64 < D /\ off + n <= N ==>
  B + off + n < D /\ n + 64 < D
Proof
  decide_tac
QED

Theorem tuple_place_child_intervals_apart:
  (B + N <= C \/ C + M <= B) /\ off + n <= N /\ pos + m <= M ==>
  B + off + n <= C + pos \/ C + pos + m <= B + off
Proof
  decide_tac
QED

Theorem tuple_place_dynamic_child_contained:
  i < live /\ live <= cap ==>
  32 + i * stride + stride <= 32 + cap * stride
Proof
  strip_tac >>
  `i < cap` by decide_tac >>
  drule array_index_element_end_bound >>
  disch_then (qspec_then `stride` mp_tac) >> decide_tac
QED

Theorem tuple_place_field_head_contained:
  type_memory_size tv <= type_memory_size_list (tv::tvs)
Proof
  simp[type_memory_size_def]
QED

Theorem tuple_place_field_tail_contained:
  type_memory_size tv + type_memory_size_list tvs =
  type_memory_size_list (tv::tvs)
Proof
  simp[type_memory_size_def]
QED

Theorem tuple_place_fixed_child_bounds:
  B + N * stride < D /\ N * stride + 64 < D /\ i < N ==>
  B + i * stride + stride < D /\ stride + 64 < D
Proof
  strip_tac >>
  `i * stride + stride <= N * stride` by
    (irule array_index_element_end_bound >> simp[]) >>
  decide_tac
QED

Theorem tuple_place_dynamic_child_bounds:
  B + (32 + cap * stride) < D /\
  (32 + cap * stride) + 64 < D /\ i < live /\ live <= cap ==>
  B + (32 + i * stride) + stride < D /\ stride + 64 < D
Proof
  strip_tac >>
  `32 + i * stride + stride <= 32 + cap * stride` by
    (irule tuple_place_dynamic_child_contained >> goal_assum drule >> simp[]) >>
  decide_tac
QED

Theorem tuple_place_field_head_bounds:
  B + type_memory_size_list (tv::tvs) < D /\
  type_memory_size_list (tv::tvs) + 64 < D ==>
  B + type_memory_size tv < D /\ type_memory_size tv + 64 < D
Proof
  simp[type_memory_size_def] >> decide_tac
QED

Theorem tuple_place_field_tail_bounds:
  B + type_memory_size_list (tv::tvs) < D /\
  type_memory_size_list (tv::tvs) + 64 < D ==>
  (B + type_memory_size tv) + type_memory_size_list tvs < D /\
  type_memory_size_list tvs + 64 < D
Proof
  simp[type_memory_size_def] >> decide_tac
QED

(* The containment interface does not require positive strides or nonempty tails. *)
Theorem tuple_place_zero_extent_probe:
  B < D /\ 64 < D ==>
  B + 0 * stride < D /\
  B + i * 0 + 0 < D /\ 0 + 64 < D
Proof
  simp[]
QED

Theorem tuple_place_empty_fields_probe:
  B < D /\ 64 < D ==>
  B + type_memory_size_list [] < D /\ type_memory_size_list [] + 64 < D
Proof
  simp[type_memory_size_def]
QED
