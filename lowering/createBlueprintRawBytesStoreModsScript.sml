(* A raw blueprint snapshot copies the live bytes, not the source capacity. *)
Theory createBlueprintRawBytesStoreMods
Ancestors
  createBlueprintRawBytesStore createExprSizeExitDefsMods
  createCtorStraightBand createCtorMaterializeStoreMods abiEncodeMaterializeExec abiEncodeMaterialize
  logBytesSeqPtr bodyCopyMemoryBase bytesCopyCode bodyPtrIfExpBytesCounted
  bodyFullMemoryFrames bodyFullUnwrapRun bodyMemoryDefs instSeqPtrLo
  valueCopyBytes representationCleanPtr assignTuplePtrCopyLen reasonCopySourcePtr
  ghostObservationPtr fragGasSeqPtr memSafeRun unitTransformDefs freshWrites valueEncodingProps
  stateRelProj exprSimCopy exprSimProps exprSimStorageCopy fragExec fragExecMem exprLoweringProps loweringPosts
  bodyPtrDefs loweringStateRelDefs ptrDiscipline context compileEnv
  venomMemDefs venomExecSemantics venomInst venomState valueEncodingDefs
  vfmConstants arithmetic relation rich_list list words finite_map pred_set

Theorem create_blueprint_raw_bytes_store_arrival_mods:
  compile_store_memory ce (Var src) (Var p) ty ty su = ((),cs) /\
  is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv (BytesV bytes) /\ val_wf tv (BytesV bytes) /\
  N = type_memory_size tv /\ type_memory_bytes ce ty = N /\ N + 64 < dimword (:256) /\
  is_bytestring_type phys /\ evaluate_type (get_tenv cx) phys = SOME pv /\
  value_has_type pv (BytesV bytes) /\
  m = val_store_size pv (BytesV bytes) /\ m <= N /\
  (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
     val_in_memory pv (BytesV bytes) (w2n sw) mem) /\
  lookup_var src z = SOME sw /\ lookup_var p z = SOME dw /\
  not_fresh_at su src /\ not_fresh_at su p /\
  ptr_covers G tn src z m /\ w2n sw + m <= z.vs_alloca_next /\
  ptr_covers G tn p z N /\ w2n dw + N <= z.vs_alloca_next /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (w2n dw,N) /\
  sa.cs_next_id <= inst.inst_id /\ sa.cs_next_var <= su.cs_next_var /\
  (!name b len. local_region ce ee.scopes z name b len ==>
    w2n dw + N <= b \/ b + len <= w2n dw) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
    w2n dw + N <= b \/ b + len <= w2n dw) /\
  fn_has_code su cs func /\ fn_inst_ids_distinct func /\
  ~z.vs_halted /\ z.vs_current_bb = su.cs_current_bb /\
  z.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  local_ptrs_reserved ce su /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at su x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at su x) /\
  return_buf_frame d ce su z /\
  (!x. old = Var x ==> not_fresh_at su x) /\ eval_operand old z = SOME ow /\
  HP H0 /\ (!H. HP H ==> stmt_state_rel H ctx func ce cx ee z /\
                         immutable_frame_mods func ce cx ee z /\
                         ghost_inv_at_mods (DF H) lo d ce cx ee G tn z) /\
  wb_frame ce es ee sa s0 z /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn ==>
  ?t Gt tt.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
      su.cs_next_id <= i.inst_id /\ i.inst_id < cs.cs_next_id /\
      i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) z t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G,tn) [] (OK t,Gt,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = cs.cs_current_bb /\
    t.vs_inst_idx = LENGTH cs.cs_current_insts /\
    val_in_memory tv (BytesV bytes) (w2n dw) t.vs_memory /\
    lookup_var p t = SOME dw /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,N) /\
    ptr_covers Gt tt p t N /\ not_fresh_at cs p /\
    eval_operand old t = SOME ow /\ (!x. old = Var x ==> not_fresh_at cs x) /\
    t.vs_allocas = z.vs_allocas /\ t.vs_alloca_next = z.vs_alloca_next /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    return_buf_frame d ce cs t /\
    (!H. HP H ==> stmt_state_rel H ctx func ce cx ee t /\
                  immutable_frame_mods func ce cx ee t /\
                  ghost_inv_at_mods (DF H) lo d ce cx ee Gt tt t) /\
    wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gt tt
Proof
  cheat
QED
