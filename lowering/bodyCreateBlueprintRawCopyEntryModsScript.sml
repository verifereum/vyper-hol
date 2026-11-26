(* Linked allocation and qualified source unwrap at a raw blueprint copy entry. *)
Theory bodyCreateBlueprintRawCopyEntryMods
Ancestors
  bodyIfExpAllocMods bodyIfExpArmUnwrapMods bodyQualifiedSnapshotStoreEntryMods
  bodyFullPostsMods bodyFullAllocaFresh bodyMemoryDefs bodyPtrIfExpAllocCompiler
  bodyFullShadowBodyInv bodyPtrDefs fragGasOriginPtr exprSimWordArgs
  exprLowering compileEnv loweringPosts loweringStateRelDefs
  exprSimProps exprSimAlloc freshWrites stateRelProj
  vyperEvalExprPreservesScopesDom vyperStorageFootprint
  vyperInterpreter vyperState venomState finite_map words arithmetic
Libs pairLib

Theorem blueprint_raw_copy_entry_mods:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_alloc_buffer (type_memory_bytes ce (vv_type vv)) sm = (buf,sn) /\
  unwrap_value ce vv sn = (op,sc) /\
  fn_has_code sm sn func /\ fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  type_memory_bytes ce (vv_type vv) < dimword (:256) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size ptv /\
  type_memory_size ptv < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size ltv /\
  0 < type_memory_size ltv /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  read_result cx tv ee = (INL (BytesV bs),ee) /\
  value_has_type ptv (BytesV bs) /\ value_has_type ltv (BytesV bs) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> 
      vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok ce e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sm s /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q dw z Gz tz x sw.
    buf.buf_operand = Var q /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       expr_post_mods H ctx func ce cx e es sa sc s0 ee (BytesV bs) op z /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gz tz /\
    (!v. not_fresh_at sm v ==> lookup_var v z = lookup_var v s /\
         FLOOKUP Gz v = FLOOKUP G v /\ op_taint tz (Var v) = op_taint tn (Var v)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = s.vs_labels /\ ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ return_buf_frame d ce sc z /\
    not_fresh_at sc q /\ lookup_var q z = SOME dw /\
    ptr_covers Gz tz q z (type_memory_bytes ce (vv_type vv)) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_bytes ce (vv_type vv)) /\
    FLOOKUP Gz q = SOME (w2n dw,type_memory_bytes ce (vv_type vv)) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce (vv_type vv)))] [q]) (fn_insts func) /\
    lo <= w2n dw /\ w2n dw + type_memory_bytes ce (vv_type vv) <= z.vs_alloca_next /\
    (!name b len. local_region ce ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_bytes ce (vv_type vv)) b len) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n dw) (type_memory_bytes ce (vv_type vv)) b len) /\
    op = Var x /\ not_fresh_at sc x /\ lookup_var x z = SOME sw /\
    val_wf ltv (BytesV bs) /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
       val_in_memory ltv (BytesV bs) (w2n sw) mem) /\
    ptr_covers Gz tz x z (type_memory_size ltv) /\
    w2n sw + type_memory_size ltv <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v rt. read_result cx tv ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt ==>
    value_has_type rt v` by simp[] >>
  mp_tac (Q.INST [`n` |-> `type_memory_bytes ce (vv_type vv)`, `k` |-> `sn`]
    ifexp_arm_result_alloc_mods) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then (qx_choosel_then [`p`,`dw0`,`u`,`Ga`,`ta`,`raw`]
    (map_every assume_tac o CONJUNCTS)) >>
  `buf.buf_operand = Var p /\ buf.buf_size = type_memory_bytes ce (vv_type vv)` by
    ((conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  cheat
QED
