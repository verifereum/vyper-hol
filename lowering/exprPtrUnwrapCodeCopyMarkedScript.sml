(* Consumer boundary: runtime immutable aggregates use the typed allocation size. *)
Theory exprPtrUnwrapCodeCopyMarked
Ancestors
  exprPtrUnwrapCodeCopyRead exprPtrUnwrapCode exprPtrUnwrapCodeEdges
  exprPtrUnwrapTypedSize exprSimUnwrapProps valueEncodingTyping valueEncodingProps
  bodyPtrDefs loweringPosts compileEnv context words arithmetic vyperState
  gasSummaryComposePtr gasSummary finite_map exprSimMemorySource

Theorem unwrap_code_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lowered_value_type cenv e = expr_type e /\
  (!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes cenv (expr_type e) = type_memory_size ty /\
    type_memory_size ty < 2**64) /\
  ghost_inv ret cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret cenv cx ee H tf z /\
    ptr_val_ok cx (expr_type e) v op H tf z /\ ptr_buf_ok cenv e op H z /\
    ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_lowered] >>
  drule_all vv_post_code_source >> strip_tac >>
  `?ty. evaluate_type (get_tenv cx) t = SOME ty /\ val_wf ty v` by
    (fs[immutable_holds_def, read_result_def, return_def] >>
     metis_tac[value_has_type_val_wf]) >>
  `type_memory_bytes cenv t = type_memory_size ty /\ type_memory_size ty < 2**64` by
    metis_tac[] >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[vv_post_read_result] >>
  `ptr_vv_ok cx (expr_type e) (Value v) (LocatedValue t p) ee G tn s` by
    fs[ptr_vv_ok_def] >>
  `compile_ensure_in_memory p.ptr_operand LocCode (type_memory_bytes cenv t)
    ((type_memory_bytes cenv t+31) DIV 32) F cenv.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
     simp[unwrap_runtime_code_route]) >>
  `32*((type_memory_bytes cenv t+31) DIV 32) = type_memory_bytes cenv t` by
    metis_tac[unwrap_typed_buffer_count, type_memory_size_slots] >>
  `type_memory_bytes cenv t < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  `?H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx (Value v))
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret cenv cx ee H tf z /\
    ptr_val_ok cx (expr_type e) v op H tf z /\ ptr_buf_ok cenv e op H z /\
    ghost_kept cenv es sa Gi ti s0 H tf` by
    (qpat_assum `post_value_type cenv e = expr_type e`
       (fn th => rewrite_tac[GSYM th]) >>
     irule unwrap_code_ensure_marked_read_ptr >> ntac 10 (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     qexistsl [`cenv.ce_imm_alloca`, `((type_memory_bytes cenv t+31) DIV 32)`,
       `type_memory_bytes cenv t`, `ty`] >> gvs[]) >>
  pop_assum strip_assume_tac >> qexistsl [`v`, `H`, `tf`, `z`] >> simp[] >>
  fs[gas_marked_exec_ptr_def, read_result_def, return_def] >>
  metis_tac[read_result_gas_obs]
QED
