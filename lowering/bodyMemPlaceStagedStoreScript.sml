(* Checked staging prefix for the parameterized memory-store continuation. *)
Theory bodyMemPlaceStagedStore
Ancestors
  bodyDeclMemoryCore entryDecoderHistoryFrame typedBytesArrayMem
  memContinuation exprLoweringProps compileEnv venomState rich_list
  fragExec fragExecMem instIdxIndep list entrySinkExtraction
  exprSimAlloc exprSimBufferStore

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
    w2n w + n <= u.vs_alloca_next /\ w2n w + n < dimword (:256) /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    (!p k. p+k <= w2n w \/ w2n w+n <= p ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) n b len) /\
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
  drule_all buffer_alloc_code >> strip_tac >>
  qpat_assum `stmt_state_rel ctx func ce cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _`) mp_tac literal_alloc_buffer_run) >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  `a.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `n < dimword (:256) /\ val_in_memory tv v (w2n sw) a.vs_memory` by simp[] >>
  drule_all buffer_copy_memory_encoding >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq (emitted_insts sm sn) _ = OK t` >>
  gvs[eval_operand_def, lookup_var_def] >>
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
  qpat_assum `run_inst_seq (emitted_insts sa sn) s = OK t`
    (mp_then Any mp_tac run_inst_seq_preserves_entry_control) >>
  simp[] >> strip_tac >> gvs[same_blocks_def, lookup_var_def] >>
  qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` kall_tac >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
