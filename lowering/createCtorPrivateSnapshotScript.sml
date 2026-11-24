(* The allocating snapshot and the supplied traversal have the same first
   arrival. Keep the ghosts constructed by allocation, unwrap, and store. *)
Theory createCtorPrivateSnapshot
Ancestors
  createCtorMaterializeSource createCtorMaterializeStore bodyFullMaterializedOperandEndpointProps
  createCtorSegmentArrival bodyFullExtCallPosList bodyFullExtCallPosAggregate
  abiEncodeArgsCase exprSimSource exprSimProps exprBodyPreProps exprOperandVar
  exprLowering exprLoweringProps stmtLoweringMono bodyMemoryDefs
  loweringPosts loweringStateRelDefs bodyPtrDefs stateRelProj
  exprSimWordArgs wordArgsPtr bodyFullPathHistory fragGasOriginPtrLoop fragExec
  context compileEnv vyperState vyperStorageTrace vyperStorageFootprint valueEncodingProps
  exprSimHyps aggregateEvaluatedLayout abiBufferAllocationCode
  venomState venomInst relation arithmetic list finite_map words freshWrites createCtorSnapshotForward
Libs horizonTypeLib

Theorem ctor_private_snapshot_actual:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) sm = (saved,sb) /\
  expr_body_pre ce cx env e es /\ ~is_word_type (lowered_value_type ce e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee raw vv s /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G s) /\
  (!tag q. vv = LocatedValue tag q /\ q.ptr_location = LocMemory ==>
    ptr_buf_ok ce e q.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
        eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ return_buf_frame d ce sa s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                (sb.cs_current_bb,LENGTH sb.cs_current_insts) /\
       ?i ms. ctor_segment_fetch func u = SOME i /\
              sm.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
              gas_origin_edge F explicit ctx func u ms (OK r)) s t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ctor_segment_fetch func t = SOME last /\ last.inst_opcode <> PHI /\
  sb.cs_next_id <= last.inst_id ==>
  ?p w tv Gt tt.
    saved = LocatedValue (lowered_value_type ce e) (mk_ptr (Var p) LocMemory) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    lookup_var p t = SOME w /\ not_fresh_at sb p /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    sm.cs_next_id < sb.cs_next_id /\ w2n w + type_memory_size tv <= t.vs_alloca_next /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    ptr_val_ok cx (lowered_value_type ce e) v (Var p) Gt tt t /\
    ptr_buf_ok ce e (Var p) Gt t /\
    (!n b len. local_region ce ee.scopes t n b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gt,tt) /\
      !xs. extcall_positional_post T DF lo d ctx func ce cx env xs [e] [saved]
        sa sb es s0 G0 tn0 H (INL [v]) ee Gt tt t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_private_snapshot_forward >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`p`,`w`,`tv`,`Gu`,`tu`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  qabbrev_tac `cut = (sb.cs_current_bb,LENGTH sb.cs_current_insts)` >>
  qabbrev_tac `C = \a b. ?i. ctor_segment_fetch func a = SOME i /\
       sm.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
       i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b` >>
  `RTC C s u` by simp[Abbr `C`] >>
  `!a b. C a b ==> (a.vs_current_bb,a.vs_inst_idx) <> cut /\
        ?i. ctor_segment_fetch func a = SOME i /\
           i.inst_opcode <> INVOKE /\ ctor_segment_next func a i = SOME b` by
    (simp[Abbr `C`] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (strip_tac >>
         `a.vs_current_bb = t.vs_current_bb /\ a.vs_inst_idx = t.vs_inst_idx` by
           fs[Abbr `cut`] >>
         `ctor_segment_fetch func a = ctor_segment_fetch func t` by
           (pure_rewrite_tac[ctor_segment_fetch_def] >> gvs[]) >>
         `i = last` by metis_tac[optionTheory.SOME_11] >> gvs[] >> decide_tac) >>
     qexists_tac `i` >> simp[]) >>
  `t = u` by
    (irule ctor_same_func_first_arrival >>
     qpat_assum `RTC (\a b. _ /\ ?i ms. _) s t` (irule_at Any) >>
     qexistsl_tac [`last`,`func`,`explicit`,`cut`,`ctx`,`C`] >>
     simp[Abbr `cut`] >> metis_tac[]) >>
  pop_assum SUBST_ALL_TAC >>
  qexistsl_tac [`p`,`w`,`tv`,`Gu`,`tu`] >> simp[] >> first_assum ACCEPT_TAC
QED

