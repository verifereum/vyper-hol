Theory placeMemoryChildForward
Ancestors
  placeMemoryCopyEffect context valueEncoding compileEnv

(* Opaque recursive hypothesis: destination membership/rank stays at callers. *)
Definition typed_memory_child_forward_def:
  typed_memory_child_forward cenv tenv ctx func dt <=>
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
    w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
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

Theorem typed_memory_child_forward_apply:
  typed_memory_child_forward cenv tenv ctx func dt /\
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
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
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
  simp[typed_memory_child_forward_def] >> metis_tac[]
QED
