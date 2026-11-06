(* Reusable raw-value to operand boundary for identity memory unwrap. *)
Theory reasonMemorySuccessPtr
Ancestors bodyPtrDefs exprSimUnwrap exprSimUnwrapProps loweringPosts
  reasonMemoryEncoderPtr reasonRaiseContinuationPtr

Theorem reason_stack_read_post_ptr:
  vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue ty op) s /\
  ptr_vv_ok cx (expr_type e) tv (StackValue ty op) ee G tn s /\
  read_result cx tv ee = (INL v,ee) ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s
Proof
  strip_tac >> drule vv_post_read_result >> strip_tac >>
  conj_tac
  >- (irule expr_post_of_vv_post_stack >> metis_tac[]) >>
  gvs[ptr_vv_ok_def]
QED

Theorem reason_memory_read_post_ptr:
  vv_post ctx func cenv cx e es sa sb s0 ee tv (LocatedValue ty p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue ty p) ee G tn s /\
  p.ptr_location = LocMemory /\ ~is_word_type ty /\
  read_result cx tv ee = (INL v,ee) ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v p.ptr_operand s /\
  ptr_val_ok cx (expr_type e) v p.ptr_operand G tn s
Proof
  strip_tac >> drule vv_post_read_result >> strip_tac >>
  conj_tac
  >- (irule expr_post_of_vv_post_memory >> metis_tac[]) >>
  gvs[vv_post_def, vv_holds_def, ptr_vv_ok_def, ptr_val_ok_def]
QED
