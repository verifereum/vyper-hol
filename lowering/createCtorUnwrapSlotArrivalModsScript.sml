(* The slot unwrap's own allocation and copy, in their emitted ID band. *)
Theory createCtorUnwrapSlotArrivalMods
Ancestors
  createCtorUnwrapSlotArrival createExprSizeExitDefsMods
  createCtorUnwrapSlotPostMods createCtorSlotLoopOriginBand createCtorStraightBand
  bodyFullUnwrapSlotOrigin exprPtrUnwrapLoopEntry exprPtrUnwrapEnsureShape
  exprPtrUnwrapSingleSegment abiBufferAllocationCode stmtReasonLitFragMemory
  exprPtrUnwrapStorage loweringPosts localPtrsProps vyperStorageFootprint
  fragGasOriginPtr ptrSafetyTransport bufferAllocationExecution venomMemProofs
  allocaHistory bodyBinopFragMemory copyExecution relation rich_list arithmetic
  venomExecSemantics venomInst venomState exprSimStorageCopy fragExec compileEnv
  exprLoweringProps exprLowering finite_map words emitHelper list ptrDiscipline
  loweringStateRelDefs venomMemDefs context bodyPtrDefs exprSimProps
  exprSimPtrTopLevelStorageCopy exprPtrUnwrapAllocSemantic abiPathAllocInv
  freshWrites valueEncodingProps exprSimFieldLayout gasOriginPtrLabels allocationPtr
  exprSimAlloc vyperStorageTrace bodyFullHashKeccakFixed loweringHalt exprPtrUnwrapAllocEntry

Theorem ctor_unwrap_slot_arrival_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  sm.cs_next_var <= sb.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id /\
  unwrap_value cenv (LocatedValue t p) sb = (op,sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block sc.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rty /\
  type_memory_size rty < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ptr_vv_ok cx (post_value_type cenv e) tv (LocatedValue t p) ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v z G' tn'.
    read_result cx tv ee = (INL v,ee) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      sb.cs_next_id <= i.inst_id /\ i.inst_id < sc.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
       expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' z) /\
    vv_at cenv cx (post_value_type cenv e) sa sc ee tv
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    vv_own cenv cx (post_value_type cenv e) sb sc ee (Value v)
       (LocatedValue (post_value_type cenv e) (mk_ptr op LocMemory)) z /\
    expr_store_bound cx (post_value_type cenv e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    alloca_history func z /\ s.vs_alloca_next <= z.vs_alloca_next /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' z /\
    ptr_buf_ok cenv e op G' z /\
    (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
            eval_operand op z = SOME w ==> w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sb x ==>
         lookup_var x z = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    wb_frame cenv ee ee sb s z /\ ghost_kept_at lo cenv ee sb G tn s G' tn'
Proof
  cheat
QED
