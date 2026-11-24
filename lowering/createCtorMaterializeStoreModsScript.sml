(* The private snapshot store runs in the original registered function.
   The pointer path and band certificate use the same sequence result. *)
Theory createCtorMaterializeStoreMods
Ancestors
  createCtorMaterializeStore createExprSizeExitDefsMods
  createCtorSegmentArrival createCtorStraightBand abiEncodeMaterializeExec abiEncodeMaterialize
  exprLoweringProps fragExecMem loweringPosts loweringStateRelDefs ptrDiscipline
  bodyFullMemoryFrames bodyCopyMemoryBase assignTuplePtrLocalFixedCopy
  logBytesSeqPtr instSeqPtrLo bodyPtrIfExpBytesCounted valueCopyBytes memSafeRun unitTransformDefs
  representationCleanPtr robustCopyTransportPtr bytesCopyCode stateRelProj
  assignTuplePtrCopyLen exprSimCopy exprSimProps exprSimStorageCopy
  exprSimWordArgs fragGasSeqPtr fragExec emitHelperProps bodyPtrDefs
  ghostObservationPtr venomMemDefs
  context compileEnv venomExecSemantics venomInst venomState valueEncodingDefs
  valueEncodingProps vfmConstants arithmetic relation rich_list list words finite_map

Theorem ctor_materialize_store_arrival_mods:
  compile_store_memory ce src (Var p) (lowered_value_type ce e)
    (lowered_value_type ce e) su = ((),sb) /\
  ~is_word_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  n = (if is_bytestring_type (lowered_value_type ce e) then val_store_size tv v
       else type_memory_size tv) /\
  fn_has_code su sb func /\ ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  (!x. src = Var x ==> not_fresh_at su x) /\ not_fresh_at su p /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (0 < n ==> w2n sw + n <= s.vs_alloca_next /\
             (?x. src = Var x /\ ptr_covers G tn x s n)) /\
  ptr_covers G tn p s (type_memory_size tv) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
  sa.cs_next_id <= inst.inst_id /\ sa.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce su /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at su x) /\
  (!name b len. local_region ce ee.scopes s name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
  (!name b len. local_region ce es.scopes s0 name b len ==>
     w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
  HP H0 /\ (!H. HP H ==> stmt_state_rel H ctx func ce cx ee s /\
                         immutable_frame_mods func ce cx ee s /\
                        ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  wb_frame ce es ee sa s0 s /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 s) ==>
  ?t Gt tt.
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
         su.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
         i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n dw) t.vs_memory /\
    lookup_var p t = SOME dw /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,type_memory_size tv) /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    ptr_val_ok cx (lowered_value_type ce e) v (Var p) Gt tt t /\
    ptr_buf_ok ce e (Var p) Gt t /\
    (!name b len. local_region ce ee.scopes t name b len ==>
       w2n dw + type_memory_size tv <= b \/ b + len <= w2n dw) /\
    (!H. HP H ==> stmt_state_rel H ctx func ce cx ee t /\
                  immutable_frame_mods func ce cx ee t /\
                  ghost_inv_at_mods (DF H) lo d ce cx ee Gt tt t) /\
    wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gt tt /\
    (~expr_has_effect e ==> pure_frame ce func es sa s0 t)
Proof
  cheat
QED
