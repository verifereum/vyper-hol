(* Posts transported along the common runtime immutable-copy execution. *)
Theory bodyFullToplevelCodePosts
Ancestors
  exprPtrUnwrapCodeCopySemantic exprPtrUnwrapCodeCopyRetained
  bodyFullUnwrapSlotPost exprPtrCleanBufferPost exprPtrUnwrapFrames
  bodyFullShared exprLowering bodyPtrDefs exprPtrCodeCopyEndpoint
  exprPtrUnwrapAllocationFrame exprPtrUnwrapRetained exprPtrUnwrapAllocSeparation
  exprLoweringProps compileEnv loweringPosts loweringStateRelDefs
  ptrDiscipline venomState venomInst finite_map arithmetic words pred_set
  bufferAllocationExecution exprSimCopy exprSimStorageCopy exprPtrUnwrapEndpointFrames

Theorem toplevel_code_runtime_semantic:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type t /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!tv. evaluate_type (get_tenv cx) t = SOME tv ==>
    type_memory_bytes cenv t = type_memory_size tv) /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee
    (Value v) (LocatedValue t p) s /\
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ copy_runtime_frame mid a sb z ==>
  expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee v op z
Proof
  strip_tac >> irule unwrap_code_copy_endpoint_post >> metis_tac[]
QED

Theorem toplevel_code_runtime_ghost:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv_at D lo ret cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  buf.buf_operand = Var root /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\
  G0 = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword (:256) /\
  nb < dimword (:256) /\ 32*n <= nb /\ a.vs_memory = s.vs_memory /\
  a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
  a.vs_call_ctx = s.vs_call_ctx /\ a.vs_immutables = s.vs_immutables /\
  copy_runtime_frame mid a sb z /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!x. not_fresh_at mid x ==>
    FLOOKUP HG x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  tf.t_mem = tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
  allocas_from lo z /\ s.vs_alloca_next <= z.vs_alloca_next ==>
  ghost_inv_at D lo ret cenv cx es HG tf z
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> irule unwrap_code_old_variable_frames >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
     goal_assum (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
     qexistsl [`k`, `sa`] >> asm_rewrite_tac[]) >>
  drule_all unwrap_code_exterior_frames >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `!name off len. local_region cenv es.scopes s name off len ==>
    w2n d+nb <= off \/ off+len <= w2n d` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `lo <= w2n d` by
    (gvs[ghost_inv_at_def, buffer_allocation_base_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     gvs[allocas_from_def] >> PairCases_on `x` >> gvs[] >> metis_tac[]) >>
  `stor_taint_ok_at D tf z` by
    (fs[ghost_inv_at_def, stor_taint_ok_at_def, copy_runtime_frame_def] >>
     qpat_x_assum `copy_static z = copy_static a`
       (mp_tac o Q.AP_TERM `\st. (st.vs_accounts,st.vs_transient,st.vs_call_ctx,st.vs_immutables)`) >>
     simp[copy_static_def] >> gvs[]) >>
  qpat_x_assum `tf.t_mem = _` kall_tac >>
  qpat_x_assum `tn0 = _` kall_tac >>
  qpat_x_assum `d = _` kall_tac >>
  irule unwrap_slot_copy_ghost_inv_at >>
  simp[] >> (conj_tac >- (fs[ghost_inv_at_def] >> decide_tac)) >>
  goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  qexistsl [`nb`, `sa`, `w2n d`] >> asm_rewrite_tac[] >>
  `nb + w2n d = w2n d + nb` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem toplevel_code_runtime_retained:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv0,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee result vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  nb < dimword (:256) /\ sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP HG x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!j. j < buffer_allocation_base s sm.cs_next_id \/
       buffer_allocation_base s sm.cs_next_id+nb <= j ==>
       (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ghost_kept_at lo cenv es sa Gi ti s0 HG tf
Proof
  strip_tac >>
  `ghost_kept cenv es sa Gi ti s0 G tn` by
    (fs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  `buffer_allocation_base s sm.cs_next_id < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  `ghost_kept cenv es sa Gi ti s0 HG tf` by
    (irule unwrap_copy_retained_post >> (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
     qexistsl [`buf`, `n2w (buffer_allocation_base s sm.cs_next_id):bytes32`, `mid`, `nb`] >>
     simp[] >> metis_tac[ADD_COMM]) >>
  `lo <= buffer_allocation_base s sm.cs_next_id` by
    (Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >>
     gvs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> gvs[] >> metis_tac[]) >>
  rewrite_tac[ghost_kept_at_def] >>
  (conj_tac >- (fs[ghost_kept_def] >> metis_tac[])) >>
  (conj_tac >- (fs[ghost_kept_def] >> metis_tac[])) >>
  (conj_tac >- (fs[ghost_kept_def] >> metis_tac[])) >>
  rpt strip_tac >>
  `i < buffer_allocation_base s sm.cs_next_id` by decide_tac >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED
