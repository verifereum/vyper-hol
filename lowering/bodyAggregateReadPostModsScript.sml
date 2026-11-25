(* Materialized Value results keep the same landing when forced: a stack
   operand is already usable, as is a nonword operand in memory. *)
Theory bodyAggregateReadPostMods
Ancestors
  bodyFullPostsMods bodyPtrDefs exprSimMemDefs exprSimUnwrap exprSimUnwrapProps
  loweringPosts vyperInterpreter vyperState

Theorem stack_value_read_post_mods:
  vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v) (StackValue t op) s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
    ee (Value v) (StackValue t op) s /\
  ptr_vv_ok cx (post_value_type ce e) (Value v) (StackValue t op) ee G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s) ==>
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op s /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s)
Proof
  simp[ptr_vv_ok_def, read_result_def, return_def] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[vv_post_mods_def, vv_holds_mods_def, expr_post_mods_def] >>
      strip_tac >> irule expr_post_of_vv_post_stack >> qexists_tac `t` >>
      simp[vv_post_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def]
QED

Theorem memory_buffer_read_post_mods:
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  vv_post_mods H ctx func ce cx e es sa sb s0 ee (Value v) (LocatedValue t p) s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
    ee (Value v) (LocatedValue t p) s /\
  ptr_vv_ok cx (post_value_type ce e) (Value v) (LocatedValue t p) ee G tn s /\
  ptr_buf_ok ce e p.ptr_operand G s ==>
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v p.ptr_operand s /\
  expr_store_bound cx (post_value_type ce e) v p.ptr_operand s /\
  ptr_val_ok cx (post_value_type ce e) v p.ptr_operand G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e p.ptr_operand G s)
Proof
  strip_tac >>
  `vv_post H ctx func ce cx e es sa sb s0 ee (Value v) (LocatedValue t p) s /\
   immutable_frame_mods func ce cx ee s` by
    (qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_mods_def, vv_holds_mods_def, vv_post_def] >>
     disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >>
  `~is_word_type (post_value_type ce e)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [vv_post_def]) >>
     qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     simp[vv_holds_def] >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  conj_tac
  >- (simp[expr_post_mods_def] >> irule expr_post_of_vv_post_memory >>
      simp[] >> qexists_tac `t` >> simp[]) >>
  simp[ptr_val_ok_def] >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_vv_ok_def, read_result_def, return_def] >> strip_tac >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def]
QED
