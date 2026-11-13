(* Posts transported along the common runtime immutable-copy execution. *)
Theory bodyFullToplevelCodePosts
Ancestors
  bodyFullToplevelCodeSource bodyFullToplevelCodeWitnessPosts
  bodyFullToplevelCodePointerPosts bodyFullToplevelCodeNormalize
  exprPtrUnwrapCodeCopySemantic exprPtrUnwrapCodeCopyRetained
  bodyFullUnwrapSlotPost exprPtrCleanBufferPost exprPtrUnwrapFrames
  bodyFullShared exprLowering bodyPtrDefs exprPtrCodeCopyEndpoint
  exprPtrUnwrapAllocationFrame exprPtrUnwrapRetained exprPtrUnwrapAllocSeparation
  exprLoweringProps compileEnv loweringPosts loweringStateRelDefs exprSimAlloc allocationPtr
  ptrDiscipline venomState venomInst finite_map arithmetic words pred_set
  bufferAllocationExecution exprSimCopy exprSimStorageCopy exprPtrUnwrapEndpointFrames
  exprPtrUnwrapAllocation

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

Theorem toplevel_code_runtime_wb_frame:
  compile_expr cenv ty (TopLevelName ann nsid) sx = (vv,sm0) /\
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ nb < dimword (:256) /\
  sb.cs_next_id <= sm.cs_next_id /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!off len. off+len <= buffer_allocation_base s sm.cs_next_id \/
     buffer_allocation_base s sm.cs_next_id+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  wb_frame cenv ee ee sb s z
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  irule unwrap_slot_copy_wb_frame >>
  (conj_tac >- simp[]) >> reverse conj_tac >- simp[] >>
  qexistsl [`nb`, `buffer_allocation_base s sm.cs_next_id`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt strip_tac >>
      `alloca_inv s` by fs[stmt_state_rel_def] >>
      once_rewrite_tac[DISJ_COMM] >>
      irule buffer_allocation_disjoint >> simp[] >>
      reverse conj_tac >- (qexists `aid` >> simp[] >> decide_tac) >>
      rpt strip_tac >> drule_all stmt_state_rel_alloca_site_bound >> simp[]) >>
  rpt strip_tac >> drule_all unwrap_alloc_local_separation >> metis_tac[]
QED

Theorem toplevel_code_runtime_posts_full:
  p.ptr_location = LocCode /\ ~is_word_type t /\ ~cenv.ce_is_ctor /\
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) /\
  (is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    is_word_type (expr_type (TopLevelName ann nsid))) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!x. vv_operand (LocatedValue t p) = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
    type_memory_bytes cenv (post_value_type cenv (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee raw (LocatedValue t p) s /\
  ghost_inv_at D lo ret cenv cx ee G tn s /\
  vv_store_bound cx (expr_type (TopLevelName ann nsid))
    (lowered_value_type cenv (TopLevelName ann nsid)) ee raw (LocatedValue t p) s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) raw (LocatedValue t p) ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  nb = type_memory_bytes cenv t /\ n = (nb+31) DIV 32 /\ imm = cenv.ce_imm_alloca /\
  compile_alloc_buffer nb sb = (buf,mid) /\
  compile_imm_copy_to_memory F imm p.ptr_operand buf.buf_operand n 0 mid = ((),sc) /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\
  buf.buf_operand = Var root /\ buf.buf_size = nb /\
  u = update_var root (n2w (buffer_allocation_base s sb.cs_next_id))
    (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := SUC s.vs_inst_idx /\
  Gm = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tm = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sb.cs_next_id) /\
  w2n d+nb < dimword(:256) /\ copy_runtime_frame mid a sc z /\
  z.vs_current_bb = sc.cs_current_bb /\ ~z.vs_halted /\
  ptr_covers Gf tnf root z nb /\ lookup_var root a = SOME d /\
  tnf.t_mem = tm.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
  tnf.t_stor = tm.t_stor /\ tnf.t_trans = tm.t_trans /\ tnf.t_imm = tm.t_imm /\
  (!x. not_fresh_at mid x ==> FLOOKUP Gf x = FLOOKUP Gm x /\
    op_taint tnf (Var x) = op_taint tm (Var x)) /\ allocas_from lo z /\
  (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) ==>
  ?v. read_result cx raw ee = (INL v,ee) /\
    expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op
      (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    ghost_inv_at D lo ret cenv cx ee Gf tnf (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee raw
        (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory))
        (z with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op
      (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_current_bb = sc.cs_current_bb /\
    (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tnf
      (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      ptr_buf_ok cenv (TopLevelName ann nsid) op Gf (z with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
    (~is_word_type (post_value_type cenv (TopLevelName ann nsid)) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
        eval_operand op (z with vs_inst_idx := LENGTH sc.cs_current_insts) = SOME w ==>
        type_memory_size rt = 0 \/ w2n w+type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf /\
    (!x. not_fresh_at sb x ==>
      lookup_var x (z with vs_inst_idx := LENGTH sc.cs_current_insts) = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    ghost_kept_at lo cenv ee sb G tn s Gf tnf
Proof
  strip_tac >>
  drule_all toplevel_code_runtime_source_post >> disch_then (qspec_then `sb` strip_assume_tac) >>
  `t = post_value_type cenv (TopLevelName ann nsid)` by
    metis_tac[exprPtrUnwrapCodeTheory.vv_post_code_source] >>
  `type_memory_bytes cenv t = type_memory_size rty /\ nb < dimword(:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
  qpat_x_assum `imm = _` SUBST_ALL_TAC >>
  drule_all toplevel_code_runtime_witness_posts >> strip_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by
    (fs[contextTheory.vv_operand_def, not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z` by
    (irule toplevel_code_runtime_semantic >> metis_tac[]) >>
  drule_all toplevel_code_runtime_witness_allocation >> strip_tac >>
  suspend "ghost"
QED

Resume toplevel_code_runtime_posts_full[ghost]:
  `sb.cs_next_var <= mid.cs_next_var` by
    (mp_tac (Q.SPECL [`nb`,`sb`] ci_mono_compile_alloc_buffer) >> simp[ci_mono_def]) >>
  `buffer_allocation_base s sb.cs_next_id < dimword(:256)` by
    (drule_all unwrap_alloc_site_bound >> decide_tac) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `root = STRING #"%" (toString sb.cs_next_var)` by
    (drule unwrap_alloc_generated_code >> strip_tac >> metis_tac[venomStateTheory.operand_11]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by metis_tac[] >>
  drule_all unwrap_alloc_taint_frame >> disch_then (qspec_then `tn` strip_assume_tac) >>
  `tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    metis_tac[] >>
  `32*n <= nb` by decide_tac >>
  drule_all toplevel_code_runtime_ghost >> strip_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> `not_fresh_at sb x` by
      (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  `!j. j < buffer_allocation_base s sb.cs_next_id \/
       buffer_allocation_base s sb.cs_next_id+nb <= j ==>
       (j IN tnf.t_mem <=> j IN tn.t_mem)` by
    (`w2n d = buffer_allocation_base s sb.cs_next_id` by
       (qpat_x_assum `d = _` (fn th => rewrite_tac[th]) >>
        simp[wordsTheory.w2n_n2w]) >>
     rpt strip_tac >>
     `j IN tm.t_mem <=> j IN tn.t_mem` by metis_tac[] >>
     `~(w2n d <= j /\ j < w2n d+32*n)` by decide_tac >>
     qpat_x_assum `tnf.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [IN_DIFF] >> metis_tac[]) >>
  drule_all toplevel_code_runtime_retained >> strip_tac >>
  suspend "pointer"
QED

Resume toplevel_code_runtime_posts_full[pointer]:
  `val_wf rty v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `type_memory_size rty <= nb /\
   type_memory_bytes cenv (lowered_value_type cenv (TopLevelName ann nsid)) <= nb` by
    (fs[lowered_value_type_def, post_value_type_def] >> decide_tac) >>
  `expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v (Var root) z` by metis_tac[] >>
  `eval_operand (Var root) z = SOME d` by metis_tac[] >>
  `~is_word_type (post_value_type cenv (TopLevelName ann nsid))` by metis_tac[] >>
  drule_all toplevel_code_runtime_pointer_posts >> strip_tac >>
  `!id path. raw <> PlaceR (MemoryPlace id path)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCode` mp_tac >>
     qpat_assum `~is_word_type (post_value_type cenv (TopLevelName ann nsid))` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, vv_holds_def, vv_at_def, post_value_type_def] >>
     metis_tac[]) >>
  `!rt. evaluate_type (get_tenv cx) (expr_type (TopLevelName ann nsid)) = SOME rt ==>
    val_wf rt v /\ type_memory_bytes cenv (expr_type (TopLevelName ann nsid)) = type_memory_size rt /\
    type_memory_bytes cenv (expr_type (TopLevelName ann nsid)) <= nb` by
    (fs[post_value_type_def] >> metis_tac[]) >>
  `!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt ==>
    type_memory_size rt <= nb` by
    (fs[lowered_value_type_def, post_value_type_def] >> metis_tac[]) >>
  drule_all toplevel_code_runtime_size_posts >> strip_tac >>
  suspend "frames"
QED

Resume toplevel_code_runtime_posts_full[frames]:
  `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s` by metis_tac[] >>
  `!off len. off+len <= buffer_allocation_base s sb.cs_next_id \/
     buffer_allocation_base s sb.cs_next_id+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (`w2n d = buffer_allocation_base s sb.cs_next_id` by
       (qpat_x_assum `d = _` (fn th => rewrite_tac[th]) >> simp[wordsTheory.w2n_n2w]) >>
     metis_tac[]) >>
  `sb.cs_next_id <= sb.cs_next_id` by simp[] >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP z.vs_allocas aid = SOME entry` by
    (`z.vs_allocas = u.vs_allocas` by
       (qpat_assum `copy_runtime_frame _ _ _ _` mp_tac >>
        qpat_assum `a = u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >>
        simp[copy_runtime_frame_def, copy_static_def, venom_state_component_equality]) >>
     qpat_assum `u = update_var _ _ _` mp_tac >>
     qpat_assum `z.vs_allocas = u.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[update_var_def, buffer_allocation_fields_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >> simp[FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = sb.cs_next_id` >> gvs[]) >>
  drule_all toplevel_code_runtime_wb_frame >> strip_tac >>
  `vv_post H ctx func cenv cx (TopLevelName ann nsid) ee sb sb s ee raw (LocatedValue t p) s` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ raw _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocCode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_post_def, vv_at_def, vv_own_def, locals_kept_def]) >>
  `ghost_kept_at lo cenv ee sb G tn s G tn` by simp[ghost_kept_at_def] >>
  `MAP FDOM ee.scopes = MAP FDOM ee.scopes` by simp[] >>
  `!x. not_fresh_at sb x ==> FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tnf (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `ghost_kept_at lo cenv ee sb G tn s Gf tnf` by
    (qpat_assum `ghost_kept_at lo cenv ee sb G tn s G tn`
       (mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) mp_tac toplevel_code_runtime_retained) >>
     disch_then drule_all >> simp[]) >>
  suspend "normalize"
QED

Resume toplevel_code_runtime_posts_full[normalize]:
  `expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op
      (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ghost_inv_at D lo ret cenv cx ee Gf tnf (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee raw
     (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory))
     (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tnf (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   ptr_buf_ok cenv (TopLevelName ann nsid) op Gf (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   wb_frame cenv ee ee sb s (z with vs_inst_idx := LENGTH sc.cs_current_insts) /\
   (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
     eval_operand op (z with vs_inst_idx := LENGTH sc.cs_current_insts) = SOME w ==>
     type_memory_size rt = 0 \/ w2n w+type_memory_size rt <= (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_alloca_next) /\
   (!x. not_fresh_at sb x ==> lookup_var x (z with vs_inst_idx := LENGTH sc.cs_current_insts) = lookup_var x s) /\
   (z with vs_inst_idx := LENGTH sc.cs_current_insts).vs_inst_idx = LENGTH sc.cs_current_insts` by
    (drule toplevel_code_runtime_normalize >> disch_then (fn th => rewrite_tac[th]) >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  qexists `v` >> simp[]
QED

Finalise toplevel_code_runtime_posts_full
