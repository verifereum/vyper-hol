Theory bodyPtrIfExpCallConsumer
Ancestors bodyPtrIfExpCallAlignment bodyPtrIfExpNoCopyAlignment
  bodyPtrDefs exprLowering vyperAST exprSimHypsDefs vyperTypeSystem

Theorem ptr_buf_ok_bytes_cong:
  type_memory_bytes ce (lowered_value_type ce e) =
    type_memory_bytes ce (lowered_value_type ce e') ==>
  (ptr_buf_ok ce e op G s <=> ptr_buf_ok ce e' op G s)
Proof
  simp[ptr_buf_ok_def]
QED

Theorem ifexp_buffer_call_arm_alignment:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\ arm = Call ann (IntCall fid) args dret /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs /\
  vv_post ctx fn ce cx arm es sa sb s0 ee tv vv t ==>
  lowered_value_type ce arm = ty
Proof
  strip_tac >>
  `expr_type arm = ty` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[] >> drule_all ifexp_buffer_call_normal_alignment >> simp[]
QED

Theorem ifexp_buffer_call_arm_ptr_post:
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\ arm = Call ann (IntCall fid) args dret /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  ce.ce_func_info (nsid_to_string fid) = (0,rbs,pvs) /\ 0 < rbs /\
  vv_post ctx fn ce cx arm es sa sb s0 ee tv vv t /\
  ~is_word_type ty /\ ptr_val_ok cx (expr_type arm) v op G tn u /\
  ptr_buf_ok ce arm op G u ==>
  ptr_mem_ok cx ty v op G tn u /\
  ptr_buf_ok ce (IfExp ty cond a b) op G u
Proof
  strip_tac >>
  `expr_type arm = ty` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  `lowered_value_type ce arm = ty` by
    metis_tac[ifexp_buffer_call_arm_alignment] >>
  (conj_tac >- gvs[ptr_val_ok_def]) >>
  `ptr_buf_ok ce arm op G u <=>
   ptr_buf_ok ce (IfExp ty cond a b) op G u` by
    (irule ptr_buf_ok_bytes_cong >>
     simp[lowered_value_type_def, expr_type_def]) >>
  gvs[]
QED
