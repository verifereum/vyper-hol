(* Retained roots at the immutable-copy endpoint use the canonical copy post. *)
Theory exprPtrUnwrapCodeCopyRetained
Ancestors
  exprPtrCodeCopyEndpoint exprPtrUnwrapEndpointFrames exprPtrUnwrapRetained
  exprPtrUnwrapAllocationFrame exprSimCopy bodyPtrDefs compileEnv loweringPosts
  venomState venomInst ptrDiscipline words arithmetic finite_map

Theorem unwrap_code_retained_post:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  vv_post ctx func cenv cx e es sa sm s0 ee result vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  nb < dimword (:256) /\ sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  buf.buf_operand = Var root /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\
  Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  copy_runtime_frame mid a sb z /\
  (!x. not_fresh_at mid x ==> FLOOKUP H x = FLOOKUP Gm x /\
    op_taint tf (Var x) = op_taint tm (Var x)) /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword (:256) /\
  32*n <= nb /\ a.vs_memory = s.vs_memory /\
  (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  tf.t_mem = tm.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} ==>
  ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     irule unwrap_code_old_variable_frames >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
     goal_assum (drule_at (Pat `_ = step_taint _ _ _ _`)) >>
     qexistsl [`k`, `sa`] >> asm_rewrite_tac[]) >>
  drule_all unwrap_code_exterior_frames >> strip_tac >>
  irule unwrap_copy_retained_post >> (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  qexistsl [`buf`, `d`, `mid`, `nb`] >> asm_rewrite_tac[] >> metis_tac[]
QED
