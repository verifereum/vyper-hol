(* Conditional posts for the fixed single-slot TopLevelName copy endpoint. *)
Theory bodyFullToplevelSlotSinglePost
Ancestors
  bodyFullUnwrapSlotPost exprPtrUnwrapStoragePost exprSimVVFrame
  exprSimMemDefs exprLoweringProps vyperStorageFootprint
  loweringPosts bodyPtrDefs venomState venomInst words arithmetic
  exprSimIfExpWidenedAdapter loweringShapeDefs
  exprPtrUnwrapStorageSource context exprLowering exprSimProps
  bodyPtrIfExpAllocCompiler allocationPtr loweringHalt

Theorem toplevel_slot_single_semantic_family:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv
      (LocatedValue t p) s) /\
  storage_holds cx tr (post_value_type cenv (TopLevelName ann nsid)) tv key ee s /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv
    (LocatedValue t p) ee G tn s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME key /\
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sb /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id < sc.cs_next_id /\
  nb < dimword (:256) /\ 32 <= nb /\ buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ slot_copy_runtime_frame mid d 1 a z /\
  ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  type_slot_size rty = 1 /\ type_memory_size rty <= nb /\
  eval_operand op z = SOME d /\
  mem_word_at (w2n d) z.vs_memory =
    slot_copy_word (if tr then TLOAD else SLOAD) s key /\
  (!b. b < 32 /\ w2n d+b IN tnf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) key) ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z) /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory rty v (w2n d) mem)
Proof
  strip_tac >> fs[post_value_type_def] >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    metis_tac[storage_holds_def] >>
  qexists `v` >> simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory rty v (w2n d) mem)` by
    (rpt strip_tac >>
     `vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv
       (LocatedValue t p) s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
     `?v'. read_result cx tv ee = (INL v',ee) /\
       expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v' op z /\
       (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
         val_in_memory rty v' (w2n d) mem)` by
       (irule (Q.INST [`n` |-> `1`] unwrap_storage_copy_post) >> simp[] >>
        goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
        goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
        goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
        qexistsl [`buf`, `k`, `mid`, `nb`, `root`] >>
        gvs[WORD_ADD_0]) >> gvs[]) >>
  fs[storage_trace_domain_def] >> metis_tac[]
QED

Theorem toplevel_slot_single_ghost_family:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo ret cenv cx ee G tn s /\
    stor_taint_ok_at (DF H) tnf z) /\
  local_ptrs_reserved cenv sb /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  local_ptrs_rel func cenv ee.scopes s /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
  lo <= w2n d /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at (DF H) lo ret cenv cx ee Gf tnf z
Proof
  rpt strip_tac >> irule unwrap_slot_copy_ghost_inv_at >>
  simp[] >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  qexistsl [`G`, `nb`, `sb`, `w2n d`, `tn`] >>
  simp[] >> metis_tac[ADD_COMM]
QED

Theorem toplevel_slot_single_cursor_frame:
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv vv s /\
  sm.cs_next_id <= sb.cs_next_id ==>
  vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv vv s
Proof
  strip_tac >> irule vv_post_alloc_mono_frame >>
  conj_tac >- fs[vv_post_def] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Theorem toplevel_slot_single_kept_frame:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) /\
  sa.cs_next_var <= sb.cs_next_var /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
  lo <= w2n d /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb.cs_next_id /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      off+sz <= b \/ b+len <= off) ==>
    off+sz <= w2n d \/ w2n d+nb <= off) /\
  (!name b len. local_region cenv es.scopes s0 name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
      off+sz <= b \/ b+len <= off) ==>
    off+sz <= w2n d \/ w2n d+nb <= off) ==>
  ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf /\
  wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s Gf tnf
Proof
  strip_tac >> rpt conj_tac
  >- (irule unwrap_slot_copy_ghost_kept_at >>
      goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
      rpt conj_tac
      >- (rpt strip_tac >>
          `w2n d+nb <= b \/ b+sz <= w2n d` by metis_tac[] >>
          `i < w2n d \/ w2n d+nb <= i` by decide_tac >> metis_tac[])
      >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
      >- (rpt strip_tac >>
          `off+sz <= w2n d \/ w2n d+nb <= off` by metis_tac[] >>
          `i < w2n d \/ w2n d+nb <= i` by decide_tac >> metis_tac[]) >>
      rpt strip_tac >> `i < w2n d` by decide_tac >> metis_tac[])
  >- (irule unwrap_slot_copy_wb_frame >> simp[] >>
      qexistsl [`nb`, `w2n d`] >> simp[] >> metis_tac[ADD_COMM]) >>
  simp[ghost_kept_at_def] >> rpt conj_tac >> rpt strip_tac
  >- (`off+sz <= w2n d \/ w2n d+nb <= off` by metis_tac[] >>
      `i < w2n d \/ w2n d+nb <= i` by decide_tac >> metis_tac[])
  >- (`w2n d+nb <= b \/ b+sz <= w2n d` by metis_tac[] >>
      `i < w2n d \/ w2n d+nb <= i` by decide_tac >> metis_tac[]) >>
  `i < w2n d` by decide_tac >> metis_tac[]
QED

Theorem toplevel_slot_single_value_posts:
  storage_holds cx tr (post_value_type cenv (TopLevelName ann nsid)) tv key ee s /\
  read_result cx tv ee = (INL v,ee) /\
  ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  type_memory_size rty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv (TopLevelName ann nsid)) <= nb /\
  eval_operand (Var root) z = SOME d /\ ptr_covers Gf tnf root z nb /\
  FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n d,nb) /\
  sa.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id < sc.cs_next_id /\
  w2n d+nb <= z.vs_alloca_next /\
  (!name b len. local_region cenv ee.scopes z name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
    val_in_memory rty v (w2n d) mem) ==>
  vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
    (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr (Var root) LocMemory)) z /\
  expr_store_bound cx (expr_type (TopLevelName ann nsid)) v (Var root) z /\
  ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v (Var root) Gf tnf z /\
  ptr_buf_ok cenv (TopLevelName ann nsid) (Var root) Gf z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
    eval_operand (Var root) z = SOME w ==>
    type_memory_size rt = 0 \/ w2n w+type_memory_size rt <= z.vs_alloca_next)
Proof
  strip_tac >> fs[post_value_type_def] >>
  `val_wf rty v /\ val_footprint rty v <= type_memory_size rty` by
    (irule storage_holds_value_bounds >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v (Var root) Gf tnf z /\
   ptr_buf_ok cenv (TopLevelName ann nsid) (Var root) Gf z` by
    (irule unwrap_storage_pointer_posts >> simp[post_value_type_def] >>
     qexists `nb` >> simp[]) >>
  simp[] >> conj_tac
  >- (simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >> gvs[] >>
      disj1_tac >>
      qexistsl [`sb.cs_next_id`, `w2n d`, `nb`] >> simp[] >> metis_tac[]) >>
  fs[post_value_type_def, lowered_value_type_def] >>
  simp[expr_store_bound_def] >> rpt strip_tac >> gvs[] >>
  imp_res_tac val_store_size_le >> decide_tac
QED

Theorem toplevel_slot_single_posts:
  compile_expr cenv ty (TopLevelName ann nsid) sa = (LocatedValue t p,sm) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sm s0 ee tv
      (LocatedValue t p) s /\ ghost_inv_at (DF H) lo ret cenv cx ee G tn s) /\
  storage_holds cx tr (post_value_type cenv (TopLevelName ann nsid)) tv key ee s /\
  ptr_vv_ok cx (post_value_type cenv (TopLevelName ann nsid)) tv
    (LocatedValue t p) ee G tn s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME key /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= mid.cs_next_var /\ sb.cs_next_id < sc.cs_next_id /\
  fn_inst_ids_distinct func /\
  ~is_word_type (post_value_type cenv (TopLevelName ann nsid)) /\
  evaluate_type (get_tenv cx) (post_value_type cenv (TopLevelName ann nsid)) = SOME rty /\
  type_slot_size rty = 1 /\ type_memory_size rty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv (TopLevelName ann nsid)) <= nb /\
  nb < dimword (:256) /\ 32 <= nb /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer nb sb = (buf,mid) /\
  fn_has_code sb mid func /\ fn_has_code mid sc func /\
  buf.buf_operand = Var root /\ buf.buf_size = nb /\ op = Var root /\
  d = n2w (buffer_allocation_base s sb.cs_next_id) /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := LENGTH mid.cs_current_insts /\
  G0 = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  slot_copy_runtime_frame mid d 1 a z /\
  mem_word_at (w2n d) z.vs_memory = slot_copy_word (if tr then TLOAD else SLOAD) s key /\
  eval_operand op z = SOME d /\ ptr_covers Gf tnf root z nb /\
  (!b. b < 32 /\ w2n d+b IN tnf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) key) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_requests = s.vs_requests /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
  alloca_history func z /\ allocas_from lo z /\
  s.vs_alloca_next <= z.vs_alloca_next /\ lo <= w2n d /\ w2n d+nb <= z.vs_alloca_next /\
  z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sb.cs_next_id /\
    (!name b len. local_region cenv ee.scopes s name b len ==> off+sz <= b \/ b+len <= off) ==>
    off+sz <= w2n d \/ w2n d+nb <= off) /\
  (!name b len. local_region cenv es.scopes s0 name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b len. local_region cenv es.scopes s0 name b len ==> off+sz <= b \/ b+len <= off) ==>
    off+sz <= w2n d \/ w2n d+nb <= off) ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
      ghost_inv_at (DF H) lo ret cenv cx ee Gf tnf z) /\
    vv_at cenv cx (post_value_type cenv (TopLevelName ann nsid)) sa sc ee tv
      (LocatedValue (post_value_type cenv (TopLevelName ann nsid)) (mk_ptr op LocMemory)) z /\
    expr_store_bound cx (expr_type (TopLevelName ann nsid)) v op z /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv (TopLevelName ann nsid)) v op Gf tnf z /\
    ptr_buf_ok cenv (TopLevelName ann nsid) op Gf z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv (TopLevelName ann nsid)) = SOME rt /\
      eval_operand op z = SOME w ==> type_memory_size rt = 0 \/
      w2n w+type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s Gf tnf
Proof
  strip_tac >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s`
    by metis_tac[toplevel_slot_single_cursor_frame] >>
  `?v. read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z) /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
      val_in_memory rty v (w2n d) mem)` by
    (rule_assum_tac (REWRITE_RULE [post_value_type_def]) >>
     irule toplevel_slot_single_semantic_family >> simp[post_value_type_def] >>
     goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
     qexistsl [`buf`, `LENGTH mid.cs_current_insts`, `mid`, `nb`, `root`, `sb`] >>
     gvs[]) >>
  `!name b len. local_region cenv ee.scopes z name b len ==>
     w2n d+nb <= b \/ b+len <= w2n d` by
    (rpt strip_tac >>
     `local_region cenv ee.scopes s name b len` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >> metis_tac[]) >>
  `z.vs_immutables = s.vs_immutables` by
    (qpat_x_assum `slot_copy_runtime_frame _ _ _ _ _` mp_tac >>
     simp[exprPtrUnwrapRuntimeFrameTheory.slot_copy_runtime_frame_def] >>
     strip_tac >>
     qpat_x_assum `copy_static _ = copy_static _`
       (mp_tac o AP_TERM ``\r:venom_state. r.vs_immutables``) >>
     simp[exprSimStorageCopyTheory.copy_static_def] >>
     Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     simp[bufferAllocationExecutionTheory.buffer_allocation_fields_def,
          venomStateTheory.update_var_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stor_taint_ok_at (DF H) tnf z` by
    (rpt strip_tac >>
     `ghost_inv_at (DF H) lo ret cenv cx ee G tn s` by metis_tac[] >>
     fs[ghost_inv_at_def, stor_taint_ok_at_def]) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    (fs[storage_trace_domain_def] >>
     `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
     fs[vv_post_def, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     ghost_inv_at (DF H) lo ret cenv cx ee Gf tnf z` by
    (rpt strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] toplevel_slot_single_ghost_family) >> simp[] >>
     conj_tac >- (goal_assum drule) >>
     qexistsl [`G`, `d`, `func`, `nb`, `s`, `sb`, `st0`, `tn`] >> gvs[] >>
     conj_tac >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
     rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  `ghost_kept_at lo cenv es sa Gi ti s0 Gf tnf /\
     wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s Gf tnf` by
    (irule (INST_TYPE [beta |-> ``:256``] toplevel_slot_single_kept_frame) >>
     conj_tac >- (goal_assum drule) >>
     goal_assum (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     conj_tac >- simp[] >>
     reverse conj_tac >- (simp[] >> goal_assum drule) >>
     qexistsl [`d`, `nb`] >> gvs[] >> rpt conj_tac >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
    (fs[storage_trace_domain_def] >>
     `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
       (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
     fs[vv_post_def]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  `?b. FLOOKUP u.vs_allocas sb.cs_next_id = SOME (b,nb) /\
       b+nb < dimword (:256) /\ eval_operand (Var root) u = SOME (n2w b)` by
    (drule_all alloca_step_site >> simp[]) >>
  `b = w2n d` by
    (qpat_x_assum `eval_operand (Var root) u = _` mp_tac >>
     simp[venomStateTheory.update_var_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     `b < dimword (:256)` by decide_tac >> simp[]) >>
  `FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n d,nb)` by
    (fs[exprPtrUnwrapRuntimeFrameTheory.slot_copy_runtime_frame_def] >>
     qpat_x_assum `a = _` (fn th => fs[th]) >> gvs[]) >>
  `eval_operand (Var root) z = SOME d` by metis_tac[] >>
  drule_all toplevel_slot_single_value_posts >> strip_tac >>
  qexists `v` >> gvs[]
QED
