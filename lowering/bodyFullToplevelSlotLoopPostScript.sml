(* Conditional posts for a fixed TopLevelName aggregate-copy endpoint. *)
Theory bodyFullToplevelSlotLoopPost
Ancestors
  bodyFullToplevelSlotSinglePost exprPtrUnwrapStoragePost
  exprPtrUnwrapRuntimeFrame exprSimCopy exprSimProps vyperStorageFootprint
  exprPtrUnwrapStorageSource exprSimVVFrame loweringPosts bodyPtrDefs
  bodyPtrIfExpAllocCompiler loweringShapeDefs bufferAllocationExecution
  venomState words arithmetic exprLoweringProps exprSimIfExpWidenedAdapter

Theorem toplevel_slot_loop_posts:
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
  n = type_slot_size rty /\ type_memory_size rty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv (TopLevelName ann nsid)) <= nb /\
  nb < dimword (:256) /\ 32*n <= nb /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer nb sb = (buf,mid) /\ fn_has_code sb mid func /\
  buf.buf_operand = Var root /\ op = Var root /\
  u = update_var root d (buffer_allocation_fields s sb.cs_next_id nb) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\ slot_copy_runtime_frame mid d n a z /\
  (!j. j < n ==> mem_word_at (w2n d+32*j) z.vs_memory =
    slot_copy_word (if tr then TLOAD else SLOAD) s (key+n2w j)) /\
  eval_operand op z = SOME d /\ ptr_covers Gf tnf root z nb /\
  (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tnf.t_mem ==>
    b IN key_taint (if tr then tn.t_trans else tn.t_stor) (key+n2w j)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_requests = s.vs_requests /\
  z.vs_immutables = s.vs_immutables /\
  (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
  FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n d,nb) /\
  alloca_history func z /\ allocas_from lo z /\
  s.vs_alloca_next <= z.vs_alloca_next /\ lo <= w2n d /\ w2n d+nb <= z.vs_alloca_next /\
  z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!name b len. local_region cenv ee.scopes s name b len ==>
    w2n d+nb <= b \/ b+len <= w2n d) /\
  (!name b len. local_region cenv ee.scopes z name b len ==>
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
    vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s /\
    ghost_inv_at (DF H) lo ret cenv cx ee G tn s` by
    metis_tac[toplevel_slot_single_cursor_frame] >>
  `?v. read_result cx tv ee = (INL v,ee)` by metis_tac[storage_holds_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v op z /\
    (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==> val_in_memory rty v (w2n d) mem)` by
    (gen_tac >> disch_tac >>
     `vv_post H ctx func cenv cx (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx ee s` by fs[vv_post_def] >>
     `?v'. read_result cx tv ee = (INL v',ee) /\
       expr_post H ctx func cenv cx (TopLevelName ann nsid) es sa sc s0 ee v' op z /\
       (!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==> val_in_memory rty v' (w2n d) mem)` by
       (rule_assum_tac (REWRITE_RULE [post_value_type_def]) >>
        irule unwrap_storage_copy_post >> simp[post_value_type_def] >>
        goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
        goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
        goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
        qexistsl [`buf`, `k`, `mid`, `nb`, `root`] >> gvs[]) >> gvs[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!mem. mem_agree_outside tnf.t_mem z.vs_memory mem ==>
    val_in_memory rty v (w2n d) mem` by metis_tac[] >>
  `local_ptrs_rel func cenv ee.scopes s` by
    ( `vv_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
        (TopLevelName ann nsid) es sa sb s0 ee tv (LocatedValue t p) s` by metis_tac[] >>
      fs[vv_post_def, stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tnf z` by
    (rpt strip_tac >>
     `ghost_inv_at (DF H) lo ret cenv cx ee G tn s` by metis_tac[] >>
     fs[ghost_inv_at_def, stor_taint_ok_at_def]) >>
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
  `eval_operand (Var root) z = SOME d` by metis_tac[] >>
  drule_all toplevel_slot_single_value_posts >> strip_tac >>
  qexists `v` >> gvs[]
QED
