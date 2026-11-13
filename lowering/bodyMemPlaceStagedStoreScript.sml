(* Checked staging prefix for the parameterized memory-store continuation. *)
Theory bodyMemPlaceStagedStore
Ancestors
  bodyDeclMemoryCore entryDecoderHistoryFrame typedBytesArrayMem
  memContinuation exprLoweringProps compileEnv venomState rich_list
  fragExec fragExecMem instIdxIndep list entrySinkExtraction

Theorem place_staging_prefix_cont:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sn func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. mem_cont_sim ctx func s u /\
    stmt_state_rel ctx func ce cx es u /\ alloca_history func u /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    w2n w + n <= u.vs_alloca_next /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  `run_inst_seq (emitted_insts sa sn) s = OK t /\
   run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> conj_tac
     >- metis_tac[run_inst_seq_append] >>
     irule run_inst_seq_mem_ok_append >> simp[]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule typed_bytes_child_seq_cont >> fs[same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `sa` >> simp[IS_PREFIX_APPEND]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule entry_straight_line_alloca_history >>
     goal_assum (drule_at Any) >> fs[same_blocks_def, IS_PREFIX_APPEND] >>
     qexistsl_tac [`s`, `sa`] >> simp[] >>
     conj_tac >- fs[stmt_state_rel_def] >>
     fs[EVERY_MEM]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sn.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx, eval_op_inst_idx, lookup_var_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  gvs[same_blocks_def, lookup_var_def]
QED
