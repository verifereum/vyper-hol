(* Normal unwrap interface: dimensions come from the semantic copy layout. *)
Theory exprPtrUnwrapStorageMarked
Ancestors
  exprPtrUnwrapStorageRead exprPtrUnwrapStorageLayout exprPtrUnwrapTypedSize
  exprPtrUnwrapStorageSource bodyPtrDefs loweringPosts exprSimProps
  exprSimFieldLayout exprSimUnwrap compileEnv context words arithmetic valueEncodingProps

Theorem unwrap_storage_marked_read_ptr:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  storage_holds cx tr (expr_type e) tv w ee s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME w /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  op_taint tn p.ptr_operand = {} /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~is_word_type (expr_type e) /\
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
  `t = expr_type e` by
    (Cases_on `tr` >> fs[vv_post_def, vv_holds_def, slot_loc_def]) >>
  drule unwrap_storage_evaluated_type >> strip_tac >>
  `type_memory_bytes cenv t = type_memory_size tv' /\
   type_memory_size tv' < 2**64` by metis_tac[] >>
  `~is_word_type t` by simp[] >>
  drule_all unwrap_slot_ensure_layout >> strip_tac >>
  `((type_memory_bytes cenv t+31) DIV 32) = type_slot_size tv'` by
    metis_tac[unwrap_typed_buffer_count] >>
  `type_slot_size tv' < 2**256` by metis_tac[unwrap_typed_buffer_count_bound] >>
  `type_memory_bytes cenv t < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  qpat_assum `post_value_type cenv e = expr_type e`
    (fn th => rewrite_tac[GSYM th]) >>
  irule unwrap_storage_ensure_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  qexistsl [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `type_memory_bytes cenv t`] >>
  gvs[type_memory_size_slots]
QED
