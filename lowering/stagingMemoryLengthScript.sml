(* Memory growth at the same counted staging endpoint. *)
Theory stagingMemoryLength
Ancestors stagingMemoryEndpoint placeMemoryTypedPrimitive
  exprSimAlloc exprSimBufferStore exprLoweringProps compileEnv venomState
  bodyDeclMemoryCore fragExec

Theorem staging_memory_endpoint_length:
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
  ?t w a u. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
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
    run_inst_seq (emitted_insts sa sm) s = OK a /\
    run_inst_seq (emitted_insts sm sn) a = OK u /\
    t = u with vs_inst_idx := LENGTH sn.cs_current_insts /\
    (!b k. b + k <= w2n w \/ w2n w + n <= b ==>
       mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all staging_memory_endpoint >>
  disch_then (qx_choosel_then [`t`, `w`, `a`, `u`] strip_assume_tac) >>
  `fn_has_code sa sm func` by
    (drule_all body_scratch_prefix_shape >> strip_tac >>
     metis_tac[fn_has_code_split]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  qpat_assum `stmt_state_rel ctx func ce cx es s`
    (mp_then Any mp_tac literal_alloc_buffer_run) >>
  disch_then (qspecl_then [`sa`, `sm`, `buf`, `n`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `a.vs_labels = s.vs_labels` by
    (drule_all exprSimAllocTheory.hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `n < dimword (:256)` by decide_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >> gvs[] >>
  simp[] >> Cases_on `n = 0` >> gvs[] >>
  metis_tac[mcopy_memory_length]
QED
