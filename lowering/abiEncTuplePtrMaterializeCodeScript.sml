(* Public pointer simulations are runtime-only (expr_sim_ptr_def and
   expr_vv_sim_ptr_def require ~ce.ce_is_ctor). Thus constructor code forcing
   is not a branch of this materialization boundary. The two general framing
   lemmas imported from MaterializeStorage apply identically to code values. *)
Theory abiEncTuplePtrMaterializeCode
Ancestors
  abiEncTuplePtrMaterializeStorage exprPtrUnwrapCodeCopyRead bodyPtrDefs

Theorem materialize_code_unwrap_owned_ptr:
  unwrap_value ce (LocatedValue t p) sm = (op,sb) /\
  compile_ensure_in_memory p.ptr_operand LocCode nb n F imm sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~ce.ce_is_ctor /\ ~is_word_type t /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  vv_post ctx fn ce cx e es sa sm s0 ee (Value v) (LocatedValue t p) s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved ce sm /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    type_memory_bytes ce t = type_memory_size ty) /\
  evaluate_type (get_tenv cx) t = SOME ty /\ val_wf ty v /\
  nb = type_memory_size ty /\ 32*((nb+31) DIV 32) = nb /\ nb < dimword (:256) /\
  type_memory_bytes ce (lowered_value_type ce e) <= nb /\
  ptr_vv_ok cx (post_value_type ce e) (Value v) (LocatedValue t p) ee G tn s /\
  ghost_inv ret ce cx ee G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  not_fresh_at sm dst /\ lookup_var dst s = SOME dw /\
  FLOOKUP s.vs_allocas aid = SOME row /\ ptr_covers G tn dst s capacity ==>
  ?H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (read_result cx (Value v))
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
  `p.ptr_location <> LocMemory` by simp[] >>
  drule_all materialize_nonmemory_vv_post_frontier >> disch_tac >>
  `ghost_kept ce ee sm G tn s G tn` by simp[ghost_kept_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ es sa sm s0 _ _ _ _` kall_tac >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes /\
   sm.cs_next_var <= sm.cs_next_var /\ sm.cs_next_id <= sm.cs_next_id` by simp[] >>
  drule_all unwrap_code_ensure_marked_read_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all materialize_owned_destination_frame >> strip_tac >>
  qexistsl [`H`, `tf`, `z`] >> simp[]
QED
