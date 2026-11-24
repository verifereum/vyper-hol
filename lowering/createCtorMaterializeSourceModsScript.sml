(* The snapshot's destination allocation is an original-function step. *)
Theory createCtorMaterializeSourceMods
Ancestors
  createCtorMaterializeSource createExprSizeExitDefsMods
  createCtorStraightBand bodyFullAllocaFresh abiBufferAllocationCode
  exprLoweringProps exprSimAlloc fragExec fragGasOriginPtr loweringStateRelDefs
  ptrDiscipline venomState venomInst venomExecSemantics finite_map list rich_list relation words
  createCtorMaterializeAllocFrameMods createCtorMaterializePhysicalMods
  createCtorUnwrapIdentityArrivalMods createCtorUnwrapRuntimeCodeArrivalMods
  createCtorUnwrapCtorCodeArrivalMods createCtorUnwrapSlotArrivalMods
  exprOperandVar exprSimProps stateRelProj exprSimSubscriptArrayFrame
  valueEncodingTyping valueCopyBytes venomExecProps arithmetic abiEncodeMaterialize
  compileEnv loweringPosts bodyPtrDefs vyperStorageFootprint bodyFullHashKeccakFixed
  context freshWrites
Libs horizonTypeLib

Theorem ctor_materialize_source_arrival_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_materialize_vv ce (lowered_value_type ce e)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (dst,sb) /\
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL pv,ee) /\ read_result cx pv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) + 64 < dimword (:256) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv s /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  (!t q. vv = LocatedValue t q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok ce e q.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx pv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\ return_buf_frame d ce sm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?buf mid su src p dw tv sw z Gz tz inst.
    dst = Var p /\ buf.buf_operand = Var p /\
    compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) sm = (buf,mid) /\
    unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) mid = (src,su) /\
    compile_store_memory ce src (Var p) (lowered_value_type ce e)
      (lowered_value_type ce e) su = ((),sb) /\
    fn_has_code su sb func /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
       sm.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       stmt_state_rel H ctx func ce cx ee z /\
       immutable_frame_mods func ce cx ee z /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv + 64 < dimword (:256) /\
    eval_operand src z = SOME sw /\ lookup_var p z = SOME dw /\
    (!x. src = Var x ==> not_fresh_at su x) /\ not_fresh_at su p /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem) /\
    (0 < type_memory_size tv ==>
       w2n sw + type_memory_size tv <= z.vs_alloca_next /\
       ?x. src = Var x /\ ptr_covers Gz tz x z (type_memory_size tv)) /\
    ptr_covers Gz tz p z (type_memory_size tv) /\
    w2n dw + type_memory_size tv <= z.vs_alloca_next /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = sm.cs_next_id /\
    FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
    sa.cs_next_id <= inst.inst_id /\ sa.cs_next_var <= su.cs_next_var /\
    local_ptrs_reserved ce su /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!name b len. local_region ce ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
    (!name b len. local_region ce es.scopes s0 name b len ==>
       regions_disjoint (w2n dw) (type_memory_size tv) b len) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 z)
Proof
  cheat
QED
