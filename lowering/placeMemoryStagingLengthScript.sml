(* Same-endpoint staging separation and memory growth. *)
Theory placeMemoryStagingLength
Ancestors
  placeMemoryStagingMem exprSimProps stmtSimAugAssignPlaceMemory bodyMemoryDefs
  fragGasPathMem stmtSimReturn exprLoweringProps compileEnv

Theorem staged_source_destination_boundary_length:
  compile_alloc_buffer (type_memory_size stv) sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src (type_memory_size stv) sm = ((),sn) /\
  fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  val_in_memory stv v (w2n sw) s.vs_memory /\ val_wf stv v /\
  val_footprint stv v <= type_memory_size stv /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dp s = SOME dw /\
  (!x. dp = Var x ==> not_fresh_at sa x) /\
  local_region ce es.scopes s name b len /\ b <= w2n dw /\
  w2n dw + type_memory_size dtv <= b + len ==>
  ?t tw. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
    return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid p. FLOOKUP s.vs_allocas aid = SOME p ==>
             FLOOKUP t.vs_allocas aid = SOME p) /\
    eval_operand buf.buf_operand t = SOME tw /\
    val_in_memory stv v (w2n tw) t.vs_memory /\
    w2n tw + type_memory_size stv <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n tw,type_memory_size stv) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
    w2n tw + type_memory_size stv < dimword (:256) /\
    (!a k. a + k <= w2n tw \/ w2n tw + type_memory_size stv <= a ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
    eval_operand dp t = SOME dw /\
    w2n dw + type_memory_size dtv <= t.vs_alloca_next /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n tw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n tw) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >> drule_all compile_staging_prefix_mem_length >>
  disch_then (qx_choosel_then [`t`, `tw`] strip_assume_tac) >>
  `local_region ce es.scopes t name b len` by
    (irule local_region_frame_fwd >> qexistsl_tac [`s`, `sa`, `es.scopes`] >>
     simp[]) >>
  `eval_operand dp t = SOME dw` by
    (drule gas_path_mem_exec >> strip_tac >>
     `t.vs_labels = s.vs_labels` by metis_tac[aug_place_path_labels] >>
     metis_tac[eval_operand_old_vars]) >>
  `b + len <= t.vs_alloca_next` by metis_tac[body_local_region_frontier] >>
  `t.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  `regions_disjoint (w2n tw) (type_memory_size stv) b len` by metis_tac[] >>
  qexistsl_tac [`t`, `tw`] >> simp[] >>
  fs[compileEnvTheory.regions_disjoint_def] >> gvs[]
QED
