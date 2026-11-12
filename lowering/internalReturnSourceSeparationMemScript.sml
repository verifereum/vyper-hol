Theory internalReturnSourceSeparationMem
Ancestors
  bodyMemoryDefs internalReturnValueEndpointMem loweringPosts

(* RESIDUAL (held): source/return-buffer disjointness; discharged once return_buf_frame carries the caller-buffer frontier *)
Theorem internal_return_source_buffer_disjoint_mem:
  body_inv tops ctx cenv cx /\ same_frame cenv ce /\
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  lowered_value_type ce e <> ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  lower_value compile_expr ce ty e sa = (op,sm) /\
  local_ptrs_reserved ce sa /\
  return_buf_frame (SOME (bw,cap)) ce sa s0 /\
  cap = type_memory_size tv /\
  w2n bw + cap + 64 < dimword (:256) /\
  expr_post ctx func ce cx e es sa sm s0 ee v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm ee v op t /\
  eval_operand op t = SOME sw ==>
  regions_disjoint (w2n sw) (type_memory_size stv) (w2n bw) cap
Proof
  cheat
QED
