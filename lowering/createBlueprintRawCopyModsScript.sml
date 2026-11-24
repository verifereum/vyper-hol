(* The copied raw singleton at the actual snapshot exit. *)
Theory createBlueprintRawCopyMods
Ancestors
  createBlueprintRawCopy createExprSizeExitDefsMods
  createBlueprintRawCopyLayoutMods createCtorMaterializeAllocFrameMods createBlueprintRawUnwrapMods
  createBlueprintRawBytesStoreMods createCtorMaterializeSourceMods createCtorSegmentArrival
  abiEncodeMaterialize abiBufferAllocationCode exprSimAlloc exprSimHyps
  exprLoweringProps fragExec fragGasOriginPtr loweringPosts loweringStateRelDefs
  stateRelProj bodyMemoryDefs bodyPtrDefs freshWrites ptrDiscipline
  vyperStorageFootprint valueEncodingDefs valueCopyBytes vyperTyping
  venomState venomInst finite_map relation words
  compileEnv exprLowering vyperState valueEncodingTyping bodyFullHashKeccakFixed
Libs horizonTypeLib

Theorem create_blueprint_raw_copy_at_cut_mods:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,cm) /\
  compile_snapshot_vv ce T vv cm = (saved,cs) /\
  eval_expr cx e es = (INL pv,ee) /\
  read_result cx pv ee = (INL (BytesV bytes),ee) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce cm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= cm.cs_next_var /\ sa.cs_next_id <= cm.cs_next_id /\
  fn_has_code cm cs func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at cm x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa cm s0 ee pv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee pv vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = cm.cs_current_bb /\
  s.vs_inst_idx = LENGTH cm.cs_current_insts /\
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
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ return_buf_frame d ce cm s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at cm x) /\ eval_operand old s = SOME ow /\
  RTC R s u /\
  (!x y. R x y ==>
    (x.vs_current_bb <> cs.cs_current_bb \/ x.vs_inst_idx <> LENGTH cs.cs_current_insts) /\
    ?ms. gas_origin_edge F explicit ctx func x ms (OK y)) /\
  u.vs_current_bb = cs.cs_current_bb /\ u.vs_inst_idx = LENGTH cs.cs_current_insts /\
  ctor_segment_fetch func u = SOME next /\ next.inst_opcode = MLOAD /\
  cs.cs_next_id <= next.inst_id ==>
  ?p w Gu tnu.
    saved = LocatedValue (vv_type vv) (mk_ptr (Var p) LocMemory) /\
    lookup_var p u = SOME w /\ not_fresh_at cs p /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (Var p) u /\
    eval_operand old u = SOME ow /\ (!x. old = Var x ==> not_fresh_at cs x) /\
    ~u.vs_halted /\ alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    return_buf_frame d ce cs u /\ wb_frame ce es ee sa s0 u /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gu tnu /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
      stmt_state_rel H ctx func ce cx ee u /\
      immutable_frame_mods func ce cx ee u /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tnu u)
Proof
  cheat
QED
