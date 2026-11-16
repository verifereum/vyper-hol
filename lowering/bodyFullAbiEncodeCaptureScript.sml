(* Actual allocation/unwrap/store capture, with witnesses outside horizons. *)
Theory bodyFullAbiEncodeCapture
Ancestors
  bodyFullAbiEncodeCaptureAlloc bodyFullAbiEncodeCaptureStore bodyFullUnwrap
  exprSimIfExpWidenedPhysicalType exprSimLayoutTransport fragExec
  freshWrites abiEncodeMaterialize exprLoweringProps vyperStorageFootprint
  loweringPosts bodyFullAllocaFresh bodyFullAbiEncodeAllocOrigin compileEnv exprSimHyps
  context exprSimProps robustCopyTransportPtr valueEncodingDefs
  bodyFullAbiEncodeOriginFloor exprOperandVar

Theorem capture_robust_lowered_source[local]:
  expr_body_pre ce cx env e es /\ ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ ptr_val_ok cx (post_value_type ce e) v src G tn s /\
  eval_operand src s = SOME w ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem
Proof
  strip_tac >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory ptv v (w2n w) mem` by
    gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- gvs[] >>
  rpt strip_tac >>
  irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
  conj_tac >- simp[] >>
  qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`,
    `get_tenv cx`, `ptv`] >> simp[]
QED

Theorem capture_store_post_frame[local]:
  expr_post H ctx func ce cx e es sa su s0 ee v src z /\
  stmt_state_rel H ctx func ce cx ee t /\
  expr_val_rel cx (post_value_type ce e) v dst t /\
  expr_val_at ce cx (post_value_type ce e) sa sb ee v dst t /\
  (post_value_type ce e <> expr_type e ==>
    expr_val_own ce cx (post_value_type ce e) sa sb ee v dst t) /\
  typed_copy_state_frame su b sz z t /\
  sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_id <= aid /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
  FLOOKUP z.vs_allocas aid = SOME (b,sz) /\ allocas_non_overlapping z /\
  (!name lb len. local_region ce es.scopes s0 name lb len ==>
    b+sz <= lb \/ lb+len <= b) ==>
  expr_post H ctx func ce cx e es sa sb s0 ee v dst t
Proof
  strip_tac >>
  `t.vs_allocas = z.vs_allocas` by
    (fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
        venomStateTheory.venom_state_component_equality]) >>
  `!off len. off+len <= b \/ b+sz <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len z.vs_memory` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x z` by
    (rpt strip_tac >>
     `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
     fs[typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
  `wb_frame ce es ee sa s0 t` by
    (irule materialize_fresh_store_frame >>
     qexistsl_tac [`aid`,`b`,`z`,`sz`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     fs[expr_post_def, wb_frame_def] >> rpt conj_tac >> metis_tac[]) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 t` by
    (strip_tac >> irule pure_frame_buffer_tail >>
     qexistsl_tac [`b`,`sz`,`inst`,`z`] >>
     fs[expr_post_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[]) >>
  fs[expr_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem capture_allocated_value[local]:
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_wf tv v /\ val_footprint tv v <= n /\
  eval_operand dst t = SOME w /\ val_in_memory tv v (w2n w) t.vs_memory /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,n) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b len. local_region ce ee.scopes t name b len ==>
    w2n w+n <= b \/ b+len <= w2n w) ==>
  expr_val_rel cx ty v dst t /\ expr_val_at ce cx ty sa sb ee v dst t /\
  expr_val_own ce cx ty sa sb ee v dst t
Proof
  strip_tac >>
  simp[expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  conj_tac >- (disj1_tac >> qexistsl_tac [`aid`,`w2n w`,`n`] >>
    simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  disj1_tac >> qexistsl_tac [`aid`,`w2n w`,`n`] >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem capture_allocated_posts[local]:
  expr_body_pre ce cx env e es_pre /\ ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  value_has_type ptv v /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  eval_operand dst t = SOME w /\ val_in_memory tv v (w2n w) t.vs_memory /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name b len. local_region ce ee.scopes t name b len ==>
    w2n w+type_memory_size tv <= b \/ b+len <= w2n w) ==>
  expr_val_rel cx (lowered_value_type ce e) v dst t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sb ee v dst t /\
  expr_val_rel cx (post_value_type ce e) v dst t /\
  expr_val_at ce cx (post_value_type ce e) sa sb ee v dst t /\
  expr_val_own ce cx (post_value_type ce e) sa sb ee v dst t
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (lowered_value_type ce e)` by metis_tac[compatible_word_type] >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  `val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
  `expr_val_rel cx (lowered_value_type ce e) v dst t /\
   expr_val_at ce cx (lowered_value_type ce e) sa sb ee v dst t /\
   expr_val_own ce cx (lowered_value_type ce e) sa sb ee v dst t` by
    (irule capture_allocated_value >> simp[] >>
     qexistsl_tac [`aid`,`type_memory_size tv`] >> simp[] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  simp[] >>
  `val_wf ptv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  drule_all materialize_post_lowered_classify >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  `val_footprint ptv v <= type_memory_size tv` by
    metis_tac[valueCopyBytesTheory.bytestring_val_footprint_le] >>
  `val_in_memory ptv v (w2n w) t.vs_memory` by
    (irule valueCopyBytesTheory.bytestring_val_in_memory_transfer >>
     conj_tac >- simp[] >>
     qexistsl_tac [`lowered_value_type ce e`,`post_value_type ce e`,`get_tenv cx`,`tv`] >>
     simp[]) >>
  irule capture_allocated_value >> simp[] >>
  qexistsl_tac [`aid`,`type_memory_size tv`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem capture_post_store_bound[local]:
  expr_body_pre ce cx env e es_pre /\ ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv u ==>
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv u
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e \/
   post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
     IF_CASES_TAC >> simp[]) >>
  Cases_on `post_value_type ce e = expr_type e` >- gvs[] >>
  `post_value_type ce e = lowered_value_type ce e` by metis_tac[] >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  gvs[exprSimMemDefsTheory.vv_store_bound_def] >>
  rpt strip_tac >> gvs[] >>
  `val_store_size rty v <= type_memory_size rty` by
    metis_tac[val_store_size_le, valueEncodingTypingTheory.value_has_type_val_wf] >>
  decide_tac
QED

Theorem abi_encode_capture_endpoint_origin:
  compile_expr ce ety e sa = (vv,sm) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv sm = (dst,sb) /\
  expr_body_pre ce cx env e es_pre /\ ~is_word_type (expr_type e) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        value_has_type rt v /\ w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) ==>
  ?t Gt tt xd dw.
    dst = Var xd /\ lookup_var xd t = SOME dw /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt) /\
      ghost_inv_at (DF H) lo d ce cx ee Gt tt t /\
      ghost_kept_at lo ce es sa Gi ti s0 Gt tt) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size tv) /\
    FLOOKUP Gt xd = SOME (w2n dw,type_memory_size tv) /\
    ptr_covers Gt tt xd t (type_memory_size tv) /\
    ptr_val_ok cx (lowered_value_type ce e) v dst Gt tt t /\
    ptr_buf_ok ce e dst Gt t /\
    (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    w2n dw + type_memory_size tv < dimword (:256) /\
    w2n dw + type_memory_size tv <= t.vs_alloca_next /\
    lo <= w2n dw /\
    (!name b sz. local_region ce es.scopes s0 name b sz ==>
      b+sz <= w2n dw \/ w2n dw+type_memory_size tv <= b) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func ce cx e es sa sb s0 ee v dst t) /\
    expr_val_rel cx (lowered_value_type ce e) v dst t /\
    expr_val_at ce cx (lowered_value_type ce e) sa sb ee v dst t
Proof
  strip_tac >>
  drule materialize_compile_trace >> strip_tac >>
  `ci_mono sm mid /\ ci_mono mid su /\ ci_mono su sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_unwrap_value,
      ci_mono_compile_store_memory, pairTheory.SND] >>
  `cs_extends sm mid /\ cs_extends mid su /\ cs_extends su sb` by
    gvs[ci_mono_def] >>
  `cs_extends mid sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sm mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code mid su func /\ fn_has_code su sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `vv_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e es sa sm s0 ee raw vv s` by
    metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[vv_post_def] >>
  `type_memory_bytes ce (lowered_value_type ce e) < dimword (:256)` by decide_tac >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  rename1 `lookup_var q u = SOME w` >>
  rename1 `ptr_covers Ga ta q u _` >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  `lo <= u.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv u /\
    ghost_inv_at (DF H) lo d ce cx ee Ga ta u /\
    ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee Ga ta u /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op Ga u) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand Ga u) /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv u /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx raw ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside ta.t_mem u.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem))` by
    (gen_tac >> strip_tac >>
     `vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
      ghost_inv_at (DF H) lo d ce cx ee G tn s` by metis_tac[] >>
     irule abi_encode_capture_alloc_resources >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`G`,`w2n w + type_memory_size tv`,`s`,`tn`] >>
     simp[] >> conj_tac >- (qpat_x_assum `u with <| vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _ |> = s` mp_tac >>
       simp[venomStateTheory.venom_state_component_equality]) >>
     strip_tac >>
     qpat_x_assum `ce.ce_is_ctor /\ _ ==> _` mp_tac >>
     simp[] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv u /\
    ghost_inv_at (DF H) lo d ce cx ee Ga ta u` by metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _ /\ _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id <= mid.cs_next_id /\
   s0.vs_alloca_next <= u.vs_alloca_next` by (fs[ci_mono_def] >> decide_tac) >>
  `~u.vs_halted` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _ |> = s` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `is_word_type (post_value_type ce e) ==> is_word_type (expr_type e)` by
    metis_tac[post_value_type_nonword] >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv u` by
    (irule capture_post_store_bound >> metis_tac[]) >>
  drule_all unwrap_value_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits, compatible_word_type] >>
  `~is_word_type (post_value_type ce e)` by metis_tac[] >>
  gvs[] >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func ce cx e es sa su s0 ee v src z` by
    metis_tac[] >>
  drule_all materialize_expr_post_lowered_source >> strip_tac >>
  rename1 `eval_operand src z = SOME sw` >>
  `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
    val_in_memory tv v (w2n sw) mem` by
    metis_tac[capture_robust_lowered_source] >>
  `lookup_var q z = SOME w /\ FLOOKUP G' q = FLOOKUP Ga q /\
    op_taint tn' (Var q) = op_taint ta (Var q)` by metis_tac[] >>
  `FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv)` by
    (qpat_x_assum `wb_frame ce ee ee mid u z` mp_tac >>
     simp[wb_frame_def] >> metis_tac[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by
    metis_tac[expr_post_def] >>
  `~z.vs_halted` by
    (`gas_origin_ptr_path
        (DF (storage_trace_horizon ee.storage_trace),lo,explicit,ctx,func,PG)
        (u,Ga,ta) [] (OK z,G',tn')` by metis_tac[] >>
     drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[exit_result_def]) >>
  `op_taint tn' (Var q) = {} /\
   ptr_covers G' tn' q z (type_memory_size tv)` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func ce cx e es sa su s0 ee v src z` by metis_tac[] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `sm.cs_next_id < mid.cs_next_id` by
    (drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >>
     strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id` by
    (goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
  pop_assum strip_assume_tac >>
  `sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
   sm.cs_next_var <= su.cs_next_var /\ sa.cs_next_var <= su.cs_next_var /\
   mid.cs_next_var <= su.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved ce mid /\ local_ptrs_reserved ce su` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region ce ee.scopes z name b len ==>
      b+len <= w2n w \/ w2n w+type_memory_size tv <= b` by
    (map_every qx_gen_tac [`name`, `lb`, `len`] >> strip_tac >>
     `local_region ce ee.scopes u name lb len` by
       (qpat_x_assum `local_region ce ee.scopes z name lb len` mp_tac >>
        simp[loweringStateRelDefsTheory.local_region_def] >>
        rpt strip_tac >>
        `not_fresh_at mid p` by
          (qpat_x_assum `local_ptrs_reserved ce mid` mp_tac >>
           simp[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
        metis_tac[]) >>
     metis_tac[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name b sz. local_region ce es.scopes s0 name b sz ==>
      b+sz <= w2n w \/ w2n w+type_memory_size tv <= b` by
    (map_every qx_gen_tac [`name`, `lb`, `sz`] >> strip_tac >>
     `local_region ce ee.scopes u name lb sz` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >> simp[] >> metis_tac[vv_post_def]) >>
     metis_tac[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  (Cases_on `type_memory_size tv = 0`
  >- (`~is_bytestring_type (lowered_value_type ce e)` by
        (strip_tac >>
         drule_all assignTuplePtrLocalCompatTheory.bytestring_evaluated_shape_ptr >>
         strip_tac >> gvs[valueEncodingTheory.type_memory_size_def]) >>
      `sb = su` by
        (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
         simp[contextTheory.compile_store_memory_def, compile_copy_memory_def, comp_return_def]) >>
      `val_footprint tv v <= 0` by metis_tac[val_footprint_le] >>
      `!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
         val_in_memory tv v (w2n w) mem` by
        (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
         conj_tac >- simp[] >>
         qexistsl_tac [`z.vs_memory`, `z.vs_memory`, `0`, `w2n sw`, `tn'.t_mem`, `tn'.t_mem`] >>
         simp[mem_bytes_at_def]) >>
      `expr_val_rel cx (lowered_value_type ce e) v (Var q) z /\
       expr_val_at ce cx (lowered_value_type ce e) sa sb ee v (Var q) z /\
       expr_val_rel cx (post_value_type ce e) v (Var q) z /\
       expr_val_at ce cx (post_value_type ce e) sa sb ee v (Var q) z /\
       expr_val_own ce cx (post_value_type ce e) sa sb ee v (Var q) z` by
        (irule capture_allocated_posts >> simp[venomStateTheory.eval_operand_def] >>
         conj_tac
         >- (qexists_tac `sm.cs_next_id` >> simp[] >>
             conj_tac >- gvs[] >> conj_tac
             >- (qpat_x_assum `!name b len. local_region ce ee.scopes z _ _ _ ==> _` mp_tac >> simp[] >> metis_tac[]) >>
             qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> val_in_memory _ _ (w2n w) mem`
               (qspec_then `z.vs_memory` mp_tac) >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
         metis_tac[]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
        expr_post H ctx func ce cx e es sa sb s0 ee v (Var q) z` by
        (rpt strip_tac >>
         `expr_post H ctx func ce cx e es sa su s0 ee v src z` by metis_tac[] >>
         fs[expr_post_def] >> metis_tac[]) >>
      qexistsl_tac [`z`, `G'`, `tn'`, `w`] >>
      simp[] >>
      conj_tac
      >- (gen_tac >> strip_tac >>
          irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
          qexistsl_tac [`Ga`, `u`, `ta`] >> simp[] >> metis_tac[]) >>
      simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
           bodyPtrDefsTheory.ptr_buf_ok_def, venomStateTheory.eval_operand_def] >>
      conj_tac
      >- (qpat_x_assum `allocas_from lo u` mp_tac >>
          simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >>
          `local_region ce ee.scopes u name b sz` by
            (irule exprSimPropsTheory.local_region_frame_fwd >>
             qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
             simp[] >> metis_tac[vv_post_def]) >>
          qpat_x_assum `!name b len. local_region ce ee.scopes u _ _ _ ==> _` drule >>
          simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
      metis_tac[not_fresh_at_mono]) >>
  `?xs b cap. src = Var xs /\ FLOOKUP G' xs = SOME (b,cap) /\
    b <= w2n sw /\ w2n sw + type_memory_size tv <= b + cap` by
    (qpat_x_assum `ptr_buf_ok ce e src G' z` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_buf_ok_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `ptr_covers G' tn' xs z (type_memory_size tv)` by
    (simp[bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[bodyPtrDefsTheory.ptr_val_ok_def,
       venomStateTheory.eval_operand_def]) >>
  `lookup_var xs z = SOME sw /\ lookup_var q z = SOME w /\
   FLOOKUP G' q = SOME (w2n w,type_memory_size tv) /\
   op_taint tn' (Var q) = {}` by
    metis_tac[venomStateTheory.eval_operand_def] >>
  `alloca_inv z` by metis_tac[stmt_state_rel_def] >>
  `z.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_def, alloca_room_next_lt] >>
  `w2n sw + type_memory_size tv < dimword (:256) /\
   w2n w + type_memory_size tv <= z.vs_alloca_next` by decide_tac >>
  `lo <= w2n w` by
    (qpat_x_assum `allocas_from lo u` mp_tac >>
     simp[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (`gas_origin_ptr_path
        (DF (storage_trace_horizon ee.storage_trace),lo,explicit,ctx,func,PG)
        (u,Ga,ta) [] (OK z,G',tn')` by metis_tac[] >>
     `lo <= u.vs_alloca_next` by decide_tac >>
     drule_all abi_encode_origin_path_allocas_from >> simp[]) >>
  `sm.cs_next_var <= su.cs_next_var /\ sa.cs_next_var <= su.cs_next_var /\
   mid.cs_next_var <= su.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved ce su /\ not_fresh_at su q` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
   (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at su x)` by
    metis_tac[not_fresh_at_mono] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at mid x` by
    metis_tac[not_fresh_at_mono] >>
  `not_fresh_at su xs` by
    (drule compiler_unwrap_value_var >>
     disch_then (qspec_then `xs` mp_tac) >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `local_ptrs_reserved ce mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name entry p sz lw. lookup_scopes name ee.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
     lookup_var p z = SOME lw ==>
     val_wf entry.type entry.value /\
     (w2n lw + val_footprint entry.type entry.value <= w2n w \/
      w2n w + type_memory_size tv <= w2n lw)` by
    (rpt strip_tac >>
     `local_ptrs_rel func ce ee.scopes z` by
       (qpat_x_assum `stmt_state_rel _ _ _ _ _ ee z` mp_tac >>
        simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
     `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
       (fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >> metis_tac[]) >>
     `local_region ce ee.scopes z name (w2n lw) sz` by
       (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
     `val_footprint entry.type entry.value <= type_memory_size entry.type` by
       metis_tac[exprSimPropsTheory.val_footprint_le] >>
     qpat_x_assum `!name b len. local_region ce ee.scopes z _ _ _ ==> _` drule >>
     strip_tac >> simp[] >> decide_tac) >>
  `!aid' off sz. FLOOKUP s0.vs_allocas aid' = SOME (off,sz) /\ aid' < sa.cs_next_id ==>
     off+sz <= w2n w \/ w2n w+type_memory_size tv <= off` by
    (rpt strip_tac >>
     `FLOOKUP s.vs_allocas aid' = SOME (off,sz)` by metis_tac[vv_post_def] >>
     `aid' < sm.cs_next_id` by decide_tac >>
     metis_tac[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d ce cx ee G' tn' z` by metis_tac[] >>
  `type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= z.vs_alloca_next` by simp[] >>
  `?t Gt tt.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (z,G',tn') [] (OK t,Gt,tt)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      ghost_inv_at (DF H) lo d ce cx ee Gt tt t /\
      ghost_kept_at lo ce es sa Gi ti s0 Gt tt) /\
    (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    lookup_var q t = SOME w /\
    FLOOKUP Gt q = SOME (w2n w,type_memory_size tv) /\
    ptr_covers Gt tt q t (type_memory_size tv) /\
    ptr_val_ok cx (lowered_value_type ce e) v (Var q) Gt tt t /\
    ptr_buf_ok ce e (Var q) Gt t /\
    (type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next) /\
    typed_copy_state_frame su (w2n w) (type_memory_size tv) z t /\
    (!p. not_fresh_at su p ==> lookup_var p t = lookup_var p z /\
      FLOOKUP Gt p = FLOOKUP G' p /\ op_taint tt (Var p) = op_taint tn' (Var p)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t` by
    (irule abi_encode_capture_store_origin >> fs[arithmeticTheory.ADD_COMM] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`sw`,`xs`] >> simp[arithmeticTheory.ADD_COMM]) >>
  `!name b len. local_region ce ee.scopes t name b len ==>
    w2n w+type_memory_size tv <= b \/ b+len <= w2n w` by
    (map_every qx_gen_tac [`name`,`lb`,`len`] >> strip_tac >>
     `local_region ce ee.scopes z name lb len` by
       (qpat_x_assum `local_region ce ee.scopes t name lb len` mp_tac >>
        simp[loweringStateRelDefsTheory.local_region_def] >> rpt strip_tac >>
        `not_fresh_at su p` by
          (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
        metis_tac[]) >>
     qpat_x_assum `!name b len. local_region ce ee.scopes z _ _ _ ==> _` drule >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `expr_val_rel cx (lowered_value_type ce e) v (Var q) t /\
   expr_val_at ce cx (lowered_value_type ce e) sa sb ee v (Var q) t /\
   expr_val_rel cx (post_value_type ce e) v (Var q) t /\
   expr_val_at ce cx (post_value_type ce e) sa sb ee v (Var q) t /\
   expr_val_own ce cx (post_value_type ce e) sa sb ee v (Var q) t` by
    (irule capture_allocated_posts >> simp[venomStateTheory.eval_operand_def] >>
     conj_tac
     >- (qexists_tac `sm.cs_next_id` >> simp[arithmeticTheory.ADD_COMM] >>
         qpat_x_assum `!mem. mem_agree_outside _ _ mem ==> val_in_memory _ _ (w2n w) mem`
           (qspec_then `t.vs_memory` mp_tac) >> simp[bodyPtrDefsTheory.mem_agree_outside_def] >>
         qpat_x_assum `!name b len. local_region ce ee.scopes t _ _ _ ==> _` mp_tac >>
         simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t` by
    (rpt strip_tac >>
     `expr_post H ctx func ce cx e es sa su s0 ee v (Var xs) z` by
       (qpat_x_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ z`
         (qspec_then `H` mp_tac) >> simp[]) >>
     `stmt_state_rel H ctx func ce cx ee z` by
       (qpat_x_assum `expr_post H ctx func ce cx e es sa su s0 ee v (Var xs) z`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [expr_post_def]) >> simp[]) >>
     irule exprSimIfExpWidenedCountedTheory.typed_copy_semantic_frame >>
     qexistsl_tac [`w2n w`,`inst`,`z`,`su`,`type_memory_size tv`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `!name b len. local_region ce ee.scopes z _ _ _ ==> _` mp_tac >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func ce cx e es sa sb s0 ee v (Var q) t` by
    (rpt strip_tac >> irule capture_store_post_frame >> simp[] >>
     qexistsl_tac [`w2n w`,`inst`,`Var xs`,`su`,`type_memory_size tv`,`z`] >>
     simp[arithmeticTheory.ADD_COMM] >> conj_tac
     >- (qpat_x_assum `!name b sz. local_region ce es.scopes s0 _ _ _ ==> _` mp_tac >>
         metis_tac[arithmeticTheory.ADD_COMM]) >>
     fs[venomMemDefsTheory.alloca_inv_def]) >>
  qexistsl_tac [`t`,`Gt'`,`tt`,`w`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (u,Ga,ta) [] (OK t,Gt',tt)` by
        metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans] >>
      metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >>
  `not_fresh_at mid x /\ not_fresh_at su x` by
    metis_tac[not_fresh_at_mono] >>
  metis_tac[])
QED

Theorem abi_encode_capture_origin:
  compile_expr ce ety e sa = (vv,sm) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv sm = (dst,sb) /\
  expr_body_pre ce cx env e es_pre /\ ~is_word_type (expr_type e) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  (!v. read_result cx raw ee = (INL v,ee) ==> value_has_type rty v) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx raw ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        value_has_type rt v /\ w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) ==>
  ?t Gt tt xd dw.
    dst = Var xd /\ lookup_var xd t = SOME dw /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt) /\
      ghost_inv_at (DF H) lo d ce cx ee Gt tt t /\
      ghost_kept_at lo ce es sa Gi ti s0 Gt tt) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size tv) /\
    FLOOKUP Gt xd = SOME (w2n dw,type_memory_size tv) /\
    ptr_covers Gt tt xd t (type_memory_size tv) /\
    ptr_val_ok cx (lowered_value_type ce e) v dst Gt tt t /\
    ptr_buf_ok ce e dst Gt t /\
    (!mem. mem_agree_outside tt.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem) /\
    w2n dw + type_memory_size tv < dimword (:256) /\
    w2n dw + type_memory_size tv <= t.vs_alloca_next /\
    lo <= w2n dw /\
    (!name b sz. local_region ce es.scopes s0 name b sz ==>
      b+sz <= w2n dw \/ w2n dw+type_memory_size tv <= b) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gt x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t
Proof
  strip_tac >> drule_all abi_encode_capture_endpoint_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`t`,`Gt'`,`tt`,`xd`,`dw`] >>
  simp[arithmeticTheory.ADD_COMM] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
