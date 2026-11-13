(* Value-facing posts on the fixed constructor TopLevelName copy run. *)
Theory bodyFullToplevelCodeCtorValuePosts
Ancestors
  bodyFullToplevelCodeCtorPosts bodyFullToplevelCodePointerPosts
  bodyFullToplevelCodeSource bodyFullToplevelCodeWitnessPosts
  exprPtrUnwrapStoragePost exprPtrUnwrapCode exprPtrUnwrapTypedSize
  exprSimCopy exprLoweringProps loweringPosts bodyPtrDefs compileEnv context
  valueEncodingProps valueTypingMemoryProps venomState venomInst words arithmetic

Theorem toplevel_code_ctor_value_posts:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee raw
    (LocatedValue t p) s /\
  read_result cx raw ee = (INL v,ee) /\
  t = post_value_type cenv (TopLevelName ann nsid) /\
  t = expr_type (TopLevelName ann nsid) /\
  p.ptr_location = LocCode /\ ~is_word_type t /\ cenv.ce_is_ctor /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_inst_ids_distinct func /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  mid.cs_next_id <= sb.cs_next_id /\
  nb = type_memory_bytes cenv t /\ nb = type_memory_size rt /\ nb < dimword(:256) /\
  evaluate_type (get_tenv cx) t = SOME rt /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  buf.buf_operand = Var root /\ op = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  a = u with vs_inst_idx := k /\ a.vs_memory = s.vs_memory /\
  stmt_state_rel H ctx func cenv cx ee a /\
  eval_operand buf.buf_operand a = SOME d /\
  compile_imm_copy_to_memory T imm src buf.buf_operand (type_slot_size rt) 0 mid = ((),sb) /\
  copy_old_operand mid src /\ copy_old_operand mid buf.buf_operand /\
  eval_operand src a = SOME q /\
  (!region. imm = SOME region ==> eval_operand region a = SOME 0w /\
    copy_old_operand mid region) /\
  copy_runtime_frame mid a sb z /\
  immutable_holds cenv cx t (Value v) q ee s /\
  w2n d + nb < dimword(:256) /\
  regions_disjoint (w2n q) nb (w2n d) nb /\
  eval_operand buf.buf_operand z = SOME d /\ ptr_covers Gf tf root z nb /\
  w2n d+nb <= z.vs_alloca_next /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword(:256) /\
  w2n q+nb <= lo /\ lo <= w2n d /\
  (!j. j IN tf.t_mem <=>
    if w2n d <= j /\ j < w2n d+nb
    then w2n q+(j-w2n d) IN tm.t_mem else j IN tm.t_mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v (w2n q) mem) ==>
  expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee v op z /\
  vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sb ee raw
    (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z /\
  expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
  ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tf z /\
  ptr_buf_ok cenv (TopLevelName ann nsid) op Gf z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    eval_operand op z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w+type_memory_size rt <= z.vs_alloca_next)
Proof
  strip_tac >>
  `vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee
    (Value v) (LocatedValue t p) s` by
    (drule_all vv_post_code_source >> strip_tac >>
     gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def]) >>
  `expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee v op z` by
    (irule toplevel_code_ctor_semantic >> metis_tac[]) >>
  `immutable_holds cenv cx t (Value v) q ee a` by
    metis_tac[immutable_holds_memory_cong] >>
  drule_all toplevel_code_ctor_contents >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  `!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
    val_in_memory rt v (w2n d) mem` by
    (irule toplevel_code_ctor_robust >> metis_tac[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv (TopLevelName ann nsid)) <= nb` by
    fs[lowered_value_type_def, post_value_type_def] >>
  `ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tf z /\
   ptr_buf_ok cenv (TopLevelName ann nsid) op Gf z` by
    (irule unwrap_storage_pointer_posts >> metis_tac[]) >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, vv_holds_def, vv_at_def, post_value_type_def] >> metis_tac[]) >>
  `!rt'. evaluate_type (get_tenv cx) (expr_type (TopLevelName ann nsid)) = SOME rt' ==>
    val_wf rt' v /\ type_memory_bytes cenv (expr_type (TopLevelName ann nsid)) = type_memory_size rt' /\
    type_memory_bytes cenv (expr_type (TopLevelName ann nsid)) <= nb` by metis_tac[] >>
  `!rt'. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt' ==>
    type_memory_size rt' <= nb` by
    (fs[lowered_value_type_def, post_value_type_def] >> metis_tac[]) >>
  drule_all toplevel_code_runtime_size_posts >> strip_tac >> metis_tac[]
QED
