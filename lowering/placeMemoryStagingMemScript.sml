(* Counted staging for place assignment.  The snapshot may overlap its source;
   only the staging allocation's separation from live locals is required. *)
Theory placeMemoryStagingMem
Ancestors
  stagingMemoryEndpoint
  bodyMemAssignTupleLocalsPrefix bodyMemAggregateBounds exprSimAlloc
  localPtrsProps stmtSimReturn loweringPosts venomState venomInst
  exprLoweringProps compileEnv bodyDeclMemoryCore loweringSlice fragExec

Theorem compile_staging_prefix_mem:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
    return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    w2n w + n <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
    w2n w + n < dimword (:256) /\
    (!name b len. local_region ce es.scopes t name b len ==>
       regions_disjoint (w2n w) n b len) /\
    (!a k. a + k <= w2n w \/ w2n w + n <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> drule_all staging_memory_endpoint >>
  disch_then (qx_choosel_then [`t`, `w`, `a`, `u`] strip_assume_tac) >>
  qpat_x_assum `t = u with vs_inst_idx := _` kall_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  `fn_has_code sa sm func` by
    (drule_all body_scratch_prefix_shape >> strip_tac >>
     metis_tac[fn_has_code_split]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  conj_tac
  >- (`t.vs_alloca_next < dimword (:256)` by
        metis_tac[alloca_room_next_lt, stmt_state_rel_def] >> decide_tac) >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
  qexistsl_tac [`ce`, `func`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]`,
    `name`, `STRING #"%" (toString sa.cs_next_var)`, `es.scopes`, `t`] >>
  simp[mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def] >>
  irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]
QED
