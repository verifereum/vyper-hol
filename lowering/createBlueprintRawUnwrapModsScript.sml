(* Plain raw-blueprint unwrap, with the already allocated snapshot destination
   carried to the same endpoint as the physical source. *)
Theory createBlueprintRawUnwrapMods
Ancestors
  createBlueprintRawUnwrap createExprSizeExitDefsMods
  createCtorMaterializePhysicalMods createCtorUnwrapIdentityArrivalMods
  createCtorUnwrapRuntimeCodeArrivalMods createCtorUnwrapCtorCodeArrivalMods
  createCtorUnwrapSlotArrivalMods exprLoweringProps exprOperandVar
  exprSimProps exprSimSubscriptArrayFrame stateRelProj allocaSiteResource
  reasonCopySourcePtr valueCopyBytes bodyMemoryDefs freshWrites
  loweringPosts bodyPtrDefs ptrDiscipline venomState finite_map
  context compileEnv vyperValue vyperState vyperTyping vyperStorageFootprint relation words

Theorem create_blueprint_raw_unwrap_store_entry_mods:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  eval_expr cx e es = (INL pv,ee) /\
  read_result cx pv ee = (INL (BytesV bytes),ee) /\
  is_bytestring_type (post_value_type ce e) /\
  is_bytestring_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  unwrap_value ce vv mid = (src,su) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= mid.cs_next_var /\ sm.cs_next_id <= mid.cs_next_id /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_has_code mid su func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block su.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa sm s0 ee pv vv a /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Ga ta a) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv a /\
  ~a.vs_halted /\ a.vs_current_bb = mid.cs_current_bb /\
  a.vs_inst_idx = LENGTH mid.cs_current_insts /\
  alloca_history func a /\ s0.vs_alloca_next <= a.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type ce e) pv vv ee Ga ta a /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op Ga a) /\
  (!t q. vv = LocatedValue t q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok ce e q.ptr_operand Ga a) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !w. eval_operand (vv_operand vv) a = SOME w ==>
      w2n w + type_memory_size rty <= lo /\
      (!mem. mem_agree_outside ta.t_mem a.vs_memory mem ==>
        val_in_memory rty (BytesV bytes) (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 Ga ta /\ return_buf_frame d ce mid a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at mid p /\ lookup_var p a = SOME dw /\ ptr_covers Ga ta p a N /\
  aid < mid.cs_next_id /\ FLOOKUP a.vs_allocas aid = SOME (w2n dw,N) /\
  (!name b len. local_region ce ee.scopes a name b len ==>
    regions_disjoint (w2n dw) N b len) ==>
  ?z Gz tz q sw.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      mid.cs_next_id <= i.inst_id /\ i.inst_id < su.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) a z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (a,Ga,ta) [] (OK z,Gz,tz) /\
      stmt_state_rel H ctx func ce cx ee z /\
      immutable_frame_mods func ce cx ee z /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func z /\ a.vs_alloca_next <= z.vs_alloca_next /\
    src = Var q /\ lookup_var q z = SOME sw /\ eval_operand src z = SOME sw /\
    not_fresh_at su q /\ not_fresh_at su p /\
    value_has_type tv (BytesV bytes) /\ val_wf tv (BytesV bytes) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      val_in_memory tv (BytesV bytes) (w2n sw) mem) /\
    ptr_covers Gz tz q z (val_store_size tv (BytesV bytes)) /\
    w2n sw + val_store_size tv (BytesV bytes) <= z.vs_alloca_next /\
    lookup_var p z = SOME dw /\ ptr_covers Gz tz p z N /\
    FLOOKUP z.vs_allocas aid = SOME (w2n dw,N) /\ w2n dw + N <= z.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes z name b len ==>
      regions_disjoint (w2n dw) N b len) /\
    (!name b len. local_region ce es.scopes s0 name b len ==>
      regions_disjoint (w2n dw) N b len) /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x a /\
      FLOOKUP Gz x = FLOOKUP Ga x /\ op_taint tz (Var x) = op_taint ta (Var x)) /\
    local_ptrs_reserved ce su /\ return_buf_frame d ce su z /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 z)
Proof
  cheat
QED
