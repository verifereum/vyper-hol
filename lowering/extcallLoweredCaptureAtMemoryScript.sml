(* Captured provenance at the physical layout used by the argument tuple. *)
Theory extcallLoweredCaptureAtMemory
Ancestors
  abiEncodeArgsSim extcallLoweredCaptureMemory exprSimProps
  valueTypingMemoryProps loweringPosts exprLowering compileEnv context vyperState

Theorem extcall_nonword_lowered_capture_at:
  expr_body_pre ce cx env e es /\
  vv_at ce cx (post_value_type ce e) sa sb ee (Value v) vv s /\
  ~is_word_type (post_value_type ce e) /\ ~is_word_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  value_has_type ltv v ==>
  vv_at ce cx (lowered_value_type ce e) sa sb ee (Value v)
    (ext_call_arg_value (lowered_value_type ce e) vv) s
Proof
  strip_tac >>
  `val_wf ltv v` by metis_tac[value_has_type_memory_wf] >>
  Cases_on `vv`
  >- (rename1 `StackValue tag op` >>
      `expr_val_at ce cx (post_value_type ce e) sa sb ee v op s` by
        gvs[vv_at_def,read_result_def,return_def] >>
      `expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op s` by
        (irule abi_args_at_lowered_transport >> metis_tac[]) >>
      simp[ext_call_arg_value_def,vv_at_def,read_result_def,return_def]) >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocMemory`
  >- (`read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def,return_def] >>
      `expr_val_at ce cx (post_value_type ce e) sa sb ee v p.ptr_operand s` by
        (drule_all vv_at_memory_val_at >> simp[]) >>
      `expr_val_at ce cx (lowered_value_type ce e) sa sb ee v p.ptr_operand s` by
        (irule abi_args_at_lowered_transport >> metis_tac[]) >>
      fs[expr_val_at_def] >>
      simp[ext_call_arg_value_def,vv_at_def,read_result_def,return_def,
           local_place_at_def] >> metis_tac[]) >>
  simp[ext_call_arg_value_def,vv_at_def,read_result_def,return_def]
QED
