(* Assemble semantic and ghost posts at one allocation/copy endpoint. *)
Theory exprPtrUnwrapStorageEndpoint
Ancestors
  exprPtrUnwrapStoragePost exprPtrUnwrapEndpointFrames
  exprPtrUnwrapStorageSource exprPtrUnwrapRuntimeFrame exprPtrUnwrapRetained
  bodyPtrDefs loweringPosts compileEnv venomState arithmetic words

Theorem unwrap_storage_endpoint_post:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  storage_holds cx tr (expr_type e) tv w ee s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME w /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  nb < dimword (:256) /\ 32*n <= nb /\ buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sm.cs_next_id nb) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ slot_copy_runtime_frame mid d n a z /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  n = type_slot_size ty /\ type_memory_size ty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= nb /\
  eval_operand (Var root) z = SOME d /\ ptr_covers H tf root z nb /\
  (!j. j < n ==> mem_word_at (w2n d+32*j) z.vs_memory =
    slot_copy_word (if tr then TLOAD else SLOAD) s (w+n2w j)) /\
  (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j)) /\
  ghost_inv ret cenv cx ee G tn s /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  d = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword (:256) /\
  a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
  a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!x. slot_copy_external mid (Var x) ==>
    FLOOKUP H x = FLOOKUP Gm x /\ op_taint tf (Var x) = op_taint tm (Var x)) /\
  (!j. j < w2n d \/ w2n d+32*n <= j ==> (j IN tf.t_mem <=> j IN tm.t_mem)) ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v (Var root) z /\
    ghost_inv ret cenv cx ee H tf z /\
    ptr_val_ok cx (expr_type e) v (Var root) H tf z /\
    ptr_buf_ok cenv e (Var root) H z /\
    ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >> drule_all unwrap_storage_copy_post >> strip_tac >>
  drule_all storage_holds_value_bounds >> strip_tac >>
  drule_all unwrap_storage_pointer_posts >> strip_tac >>
  drule_all unwrap_copy_ghost_inv >> disch_tac >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x) /\
    (!sz. ptr_covers H tf x z sz <=> ptr_covers G tn x s sz)` by
    (gen_tac >> disch_tac >> irule unwrap_copy_old_variable_frames >>
     goal_assum (drule_at (Pat `slot_copy_runtime_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >> simp[] >>
     qexistsl [`PG`, `k`, `sa`] >> asm_rewrite_tac[]) >>
  drule_all unwrap_copy_exterior_frames >> strip_tac >>
  `ghost_kept cenv es sa Gi ti s0 H tf` by
    (`!x. not_fresh_at sa x ==>
       FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
       metis_tac[] >>
     drule_all unwrap_copy_retained_post >> simp[]) >>
  qexists `v` >> simp[]
QED
