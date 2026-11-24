(* Entry resources at the data-pointer cut of a raw CREATE snapshot. *)
Theory createSizeRawSnapshotEntryMods
Ancestors
  createSizeRawSnapshotEntry createExprSizeExitDefsMods
  bodyFullUnwrapSlotPost exprPtrUnwrapAllocSemantic exprPtrUnwrapAllocEntry
  bodyMemoryDefs bodyPtrDefs ptrDiscipline decoderAllocationBoundsPtr exprSimCopy exprPtrUnwrapRetained
  exprPtrUnwrapAllocSeparation bodyFullHashKeccakFixed
  exprLowering exprLoweringProps emitHelperProps compileEnv loweringPosts
  bufferAllocationExecution allocaHistory venomState venomMemDefs
  venomExecSemantics venomMemProps venomInst finite_map pred_set words arithmetic
  exprSimAlloc exprSimStorageCopy exprPtrUnwrapAllocation
  createSizeRawMemoryFootprint createSizeRawImmutableFootprint
  createSizeRawScalarFrame createSizeRawCutHistory createSizeSlotTraversal
  exprPtrUnwrapRuntimeFrame createBlueprintRawCopyLayoutMods bodyPtrMakeArrayExternalCaller
  exprPtrUnwrapMarked externalEntryShape loweringShapeDefs abiBufferAllocationCode
  loweringHalt valueTypingMemoryProps exprSimAggregateLayout vfmConstants
  exprBodyPreProps exprSimSource exprSimHyps abiEncodeArgsCase vyperInterpreter vyperTyping valueEncodingProps valueEncodingDefs
  fragGasOrigin fragExec context copyExecution slotCopyExecution relation list rich_list
  vyperTypeSystem stateRelProj bodyPtrAttributeSource freshWrites reasonEndpointResourcesPtr
Libs BasicProvers

(* These are entry ghosts, not a claimed ghost execution. In particular,
   the bytes in the snapshot window are conservatively allowed to be tainted. *)

Theorem raw_snapshot_entry_ghost_mods[local]:
  ghost_inv_at_mods D lo d ce cx es G tn u /\ local_ptrs_reserved ce a /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  local_ptrs_rel func ce es.scopes u /\
  (!name b n. local_region ce es.scopes u name b n ==>
     (snapshot_base:num) + cap <= b \/ b + n <= snapshot_base) /\
  (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x u) /\
  (!off n. off + n <= snapshot_base \/ snapshot_base + cap <= off ==>
     mem_bytes_at off n r.vs_memory = mem_bytes_at off n u.vs_memory) /\
  ~not_fresh_at a len /\ ~not_fresh_at a data /\ lo <= snapshot_base /\
  r.vs_accounts = u.vs_accounts /\ r.vs_transient = u.vs_transient /\
  r.vs_immutables = u.vs_immutables /\ r.vs_call_ctx = u.vs_call_ctx /\
  allocas_from lo r /\ lo <= r.vs_alloca_next ==>
  ghost_inv_at_mods D lo d ce cx es (G |+ (data,snapshot_base,cap))
    (tn with <|t_var := tn.t_var |+ (len,{}) |+ (data,{});
               t_mem := tn.t_mem UNION {i | snapshot_base <= i /\ i < snapshot_base + cap}|>) r
Proof
  cheat
QED

Theorem raw_snapshot_finish_entry_mods[local]:
  compile_alloc_buffer cap a = (buf,m) /\ fn_has_code a m func /\
  buf.buf_operand = Var root /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\ cap < dimword (:256) /\
  step_inst_base (mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [root]) u = OK v /\
  snapshot_base = buffer_allocation_base u a.cs_next_id /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  alloca_history func u /\ ~u.vs_halted /\
  (?H. valid_horizon cx st0 H p.storage_trace) /\
  (!H. valid_horizon cx st0 H p.storage_trace ==>
     stmt_state_rel H ctx func ce cx (p with gas_obs := []) u /\
     immutable_frame_mods func ce cx (p with gas_obs := []) u /\
     storage_well_formed_on cx (p with gas_obs := []) (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx (p with gas_obs := []) G tn u) /\
  return_buf_frame d ce a u /\ a.cs_next_var <= ac.cs_next_var /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  copy_static r = copy_static v /\ LENGTH v.vs_memory <= LENGTH r.vs_memory /\
  (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x v) /\
  (!off k. off+k <= snapshot_base \/ snapshot_base+cap <= off ==>
    mem_bytes_at off k r.vs_memory = mem_bytes_at off k v.vs_memory) /\
  alloca_history func r /\
  r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
  ~not_fresh_at a len /\ ~not_fresh_at a data /\
  not_fresh_at ac len /\ not_fresh_at ac data /\
  lookup_var len r = SOME (n2w (LENGTH code)) /\
  lookup_var data r = SOME (n2w (snapshot_base+32)) /\ LENGTH code + 32 <= cap ==>
  ?Gr tnr.
    (!H. valid_horizon cx st0 H p.storage_trace ==>
       stmt_state_rel H ctx func ce cx (p with gas_obs := []) r /\
       immutable_frame_mods func ce cx (p with gas_obs := []) r /\
       storage_well_formed_on cx (p with gas_obs := []) (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx (p with gas_obs := []) Gr tnr r) /\
    return_buf_frame d ce ac r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
    FLOOKUP r.vs_allocas a.cs_next_id = SOME (snapshot_base,cap) /\
    lookup_var len r = SOME (n2w (LENGTH code)) /\
    lookup_var data r = SOME (n2w (snapshot_base+32)) /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    op_taint tnr (Var len) = {} /\ ptr_covers Gr tnr data r (LENGTH code) /\
    w2n (n2w (snapshot_base+32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  cheat
QED

Theorem raw_snapshot_typed_capacity_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= 49152 /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u ==>
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  LENGTH code + 32 <= type_memory_bytes ce (lowered_value_type ce e) /\
  type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
  32 * ((type_memory_bytes ce (lowered_value_type ce e) + 31) DIV 32) =
    type_memory_bytes ce (lowered_value_type ce e) /\
  (vv_location vv = SOME LocCode ==>
    type_memory_bytes ce (vv_type vv) = type_memory_bytes ce (lowered_value_type ce e))
Proof
  cheat
QED

Theorem raw_snapshot_memory_header_mods[local]:
  vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv ee u /\
  read_result cx tv ee = (INL (BytesV code),ee) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  ?s. eval_operand (vv_operand vv) u = SOME s /\ mload (w2n s) u = n2w (LENGTH code)
Proof
  cheat
QED

Theorem raw_snapshot_copy_footprint_mods[local]:
  compile_alloc_buffer cap a = (buf,m) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\ cap = type_memory_bytes ce ty /\
  fn_has_code a b func /\ B = buffer_allocation_base u a.cs_next_id /\
  B + cap < dimword (:256) /\ LENGTH code + 32 <= cap /\
  32 * ((cap + 31) DIV 32) = cap /\
  (vv_location vv = SOME LocCode ==> type_memory_bytes ce (vv_type vv) = cap) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode \/
    ?tr. vv_location vv = SOME (slot_loc tr)) /\
  local_ptrs_reserved ce a /\ stmt_state_rel H ctx func ce cx ee u /\
  vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv ee u /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) = SOME (BaseTV (BytesT (Dynamic k))) /\
  read_result cx tv ee = (INL (BytesV code),ee) /\ copy_old_operand a (vv_operand vv) /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  v.vs_current_bb = u.vs_current_bb /\ v.vs_memory = u.vs_memory /\ v.vs_inst_idx = u.vs_inst_idx /\
  run_inst_seq (emitted_insts a m) u = OK v /\
  m.cs_current_insts = a.cs_current_insts ++ emitted_insts a m /\
  m.cs_current_bb = a.cs_current_bb /\ LENGTH m.cs_current_insts = SUC (LENGTH a.cs_current_insts) /\
  buf.buf_operand = Var root /\
  copy_old_operand m buf.buf_operand /\ eval_operand buf.buf_operand v = SOME (n2w B) /\
  (!op. copy_old_operand a op ==> copy_old_operand m op /\ eval_operand op v = eval_operand op u) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
  ((!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?y exit. lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      fn_has_code m b func /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z)) ==>
  copy_static z = copy_static v /\ LENGTH v.vs_memory <= LENGTH z.vs_memory /\
  copy_old_operand b snap /\ eval_operand snap z = SOME (n2w B) /\
  (!x. not_fresh_at m x ==> lookup_var x z = lookup_var x v) /\
  (!off n. off+n <= B \/ B+cap <= off ==>
    mem_bytes_at off n z.vs_memory = mem_bytes_at off n v.vs_memory)
Proof
  cheat
QED

Theorem create_raw_snapshot_payload_entry_mods:
  expr_body_pre_mods mods ce cx env e es /\ expr_type e = BaseT (BytesT (Dynamic k)) /\ k <= 49152 /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  eval_expr cx e (es with gas_obs := obs) = (INL tv,p) /\
  read_result cx tv p = (INL (BytesV code),p) /\
  read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
  valid_horizon cx st0 H p.storage_trace /\
  vv_post_mods H ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx func ce cx (p with gas_obs := []) u /\
      storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx (p with gas_obs := []) G tn u) /\
  return_buf_frame d ce a u /\ alloca_history func u /\ ~u.vs_halted /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce a /\ fn_inst_ids_distinct func /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  compile_create_snapshot ce vv (lowered_value_type ce e) a = (snap,b) /\
  emit_op MLOAD [snap] b = (len_op,c) /\ emit_op ADD [snap; Lit 32w] c = (data_op,ac) /\
  fn_has_code a b func /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/ vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts a b) u = OK (z with vs_inst_idx := u.vs_inst_idx)) /\
  (!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf m y exit. compile_alloc_buffer (type_memory_bytes ce (lowered_value_type ce e)) a = (buf,m) /\
      fn_has_code m b func /\ lookup_block b.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      y.vs_current_bb = m.cs_current_bb /\ y.vs_inst_idx = LENGTH m.cs_current_insts /\
      z.vs_current_bb = b.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts a m) u = OK (y with vs_inst_idx := u.vs_inst_idx) /\
      RTC (\x t. (x.vs_current_bb <> b.cs_current_bb \/ x.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) y z) /\
  run_inst_seq (emitted_insts b c) z = OK (l with vs_inst_idx := z.vs_inst_idx) /\
  run_inst_seq (emitted_insts c ac) l = OK (r with vs_inst_idx := l.vs_inst_idx) /\
  RTC (\x t. ?ms. gas_origin_edge F explicit ctx func x ms (OK t)) u r /\
  eval_operand len_op l = SOME (n2w (LENGTH code)) ==>
  ?Gr tnr len data.
    len_op = Var len /\ data_op = Var data /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
       stmt_state_rel h ctx func ce cx (p with gas_obs := []) r /\
       immutable_frame_mods func ce cx (p with gas_obs := []) r /\
       storage_well_formed_on cx (p with gas_obs := []) (FST h) /\
       ghost_inv_at_mods (DF h) lo d ce cx (p with gas_obs := []) Gr tnr r) /\
    return_buf_frame d ce ac r /\ alloca_history func r /\ ~r.vs_halted /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp r) /\
    r.vs_current_bb = ac.cs_current_bb /\ r.vs_inst_idx = LENGTH ac.cs_current_insts /\
    FLOOKUP r.vs_allocas a.cs_next_id =
      SOME (buffer_allocation_base u a.cs_next_id,type_memory_bytes ce (lowered_value_type ce e)) /\
    lookup_var len r = SOME (n2w (LENGTH code)) /\
    lookup_var data r = SOME (n2w (buffer_allocation_base u a.cs_next_id + 32)) /\
    not_fresh_at ac len /\ not_fresh_at ac data /\
    op_taint tnr (Var len) = {} /\ ptr_covers Gr tnr data r (LENGTH code) /\
    w2n (n2w (buffer_allocation_base u a.cs_next_id + 32) : bytes32) + LENGTH code <= r.vs_alloca_next
Proof
  cheat
QED
