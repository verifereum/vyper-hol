(* Nonmemory physical values can be framed at the full unwrap frontier.
   Unlike memory ownership, their ownership interval does not include an alloca. *)
Theory abiEncTuplePtrMaterializeStorage
Ancestors
  exprPtrUnwrapStorageRead exprSimAggregateChildren loweringPosts bodyPtrDefs
  compileEnv context

Theorem materialize_nonmemory_vv_post_frontier:
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  p.ptr_location <> LocMemory ==>
  vv_post ctx func ce cx e ee sm sm s ee raw (LocatedValue t p) s
Proof
  simp[vv_post_def, vv_at_def, vv_own_def]
QED

Theorem materialize_owned_destination_frame:
  expr_post ctx fn ce cx e ee sm sb s ee v op z /\
  ghost_kept ce ee sm G tn s H tf /\ not_fresh_at sm dst /\
  lookup_var dst s = SOME w /\ FLOOKUP s.vs_allocas aid = SOME row /\
  ptr_covers G tn dst s capacity ==>
  lookup_var dst z = SOME w /\ FLOOKUP z.vs_allocas aid = SOME row /\
  ptr_covers H tf dst z capacity
Proof
  rw[expr_post_def, wb_frame_def, ghost_kept_def, ptr_covers_def] >>
  metis_tac[]
QED

Theorem materialize_storage_unwrap_owned_ptr:
  compile_ensure_in_memory p.ptr_operand (slot_loc tr) nb n ctor imm sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  storage_holds cx tr (post_value_type ce e) raw w ee s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME w /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue t p) ee G tn s /\
  op_taint tn p.ptr_operand = {} /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved ce sm /\ sm.cs_next_id < sb.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ty /\ n = type_slot_size ty /\
  type_memory_size ty <= nb /\ 32*n <= nb /\ nb < dimword (:256) /\ n < 2**256 /\
  type_memory_bytes ce (lowered_value_type ce e) <= nb /\
  ghost_inv ret ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  not_fresh_at sm dst /\ lookup_var dst s = SOME dw /\
  FLOOKUP s.vs_allocas aid = SOME row /\ ptr_covers G tn dst s capacity ==>
  ?v H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (read_result cx raw)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx fn ce cx e ee sm sb s ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret ce cx ee H tf z /\
    ptr_val_ok cx (post_value_type ce e) v op H tf z /\ ptr_buf_ok ce e op H z /\
    ghost_kept ce ee sm G tn s H tf /\
    lookup_var dst z = SOME dw /\ FLOOKUP z.vs_allocas aid = SOME row /\
    ptr_covers H tf dst z capacity
Proof
  strip_tac >>
  `p.ptr_location <> LocMemory` by (Cases_on `tr` >> gvs[slot_loc_def]) >>
  drule_all materialize_nonmemory_vv_post_frontier >> disch_tac >>
  `ghost_kept ce ee sm G tn s G tn` by simp[ghost_kept_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ es sa sm s0 _ _ _ _` kall_tac >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes /\
   sm.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sm.cs_next_id` by simp[] >>
  drule_all unwrap_storage_ensure_marked_read_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all materialize_owned_destination_frame >> strip_tac >>
  qexistsl [`v`, `H`, `tf`, `z`] >> simp[]
QED
