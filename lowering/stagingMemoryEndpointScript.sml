(* Shared counted snapshot staging implementation and exterior frame. *)
Theory stagingMemoryEndpoint
Ancestors
  bodyMemAssignTupleLocalsPrep bodyDeclMemoryCore bodyDeclMemoryCounted
  exprSimAlloc exprSimBufferStore abiBuiltinAllocation tupleStageProps
  fragGasPathMem fragGasMode fragGasSeqMem allocaHistoryFragment
  exprLoweringProps loweringSlice emitHelper emitHelperProps exprLowering
  compileEnv context venomState venomExecSemantics venomInst freshWrites
  valueEncoding valueEncodingProps valueTypingMemoryProps finite_map list rich_list
  localPtrsProps stmtSimDefs stmtSimProps fragExec fragExecMem bodyMemoryDefs
  loweringPosts vyperTyping instMemFrontier stmtSimReturn

Theorem staging_run_allocation[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  run_inst_seq (emitted_insts sa sm) s = OK a /\
  run_inst_seq (emitted_insts sm sn) a = OK t ==>
  ?w. eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
    (!b k. b + k <= w2n w \/ w2n w + n <= b ==>
       mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  `a.vs_labels = s.vs_labels` by
    (drule_all exprSimAllocTheory.hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand src a = SOME sw` by
    (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
  `n < dimword (:256)` by decide_tac >>
  drule_all buffer_copy_memory_run >> strip_tac >> gvs[] >>
  `sm.cs_next_var = sn.cs_next_var` by
    metis_tac[buffer_copy_memory_shape] >>
  `!b k. b + k <= w2n w \/ w2n w + n <= b ==>
     mem_bytes_at b k
       (if n = 0 then a else mcopy (w2n w) (w2n sw) n a).vs_memory =
       mem_bytes_at b k s.vs_memory` by
    (Cases_on `n = 0` >- simp[] >> simp[] >> rpt strip_tac >>
     qpat_x_assum `a.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
     irule buffer_mcopy_exterior >> simp[]) >>
  qexists_tac `w` >>
  Cases_on `n = 0` >>
  gvs[mcopy_def, write_memory_with_expansion_def, LET_THM,
      eval_operand_def, lookup_var_def, not_fresh_at_def] >> gvs[]
QED

Theorem staging_memory_endpoint:
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
       mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory)
Proof
  strip_tac >> drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  drule_all staging_run_allocation >> strip_tac >> gvs[] >>
  `run_inst_seq (emitted_insts sa sn) s = OK t` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  `return_buf_frame d ce sn t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sn)` by
    metis_tac[body_scratch_prefix_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sn)` by
    (fs[EVERY_MEM] >> metis_tac[MEM_APPEND]) >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  gvs[stmt_state_rel_inst_idx] >> conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >>
  Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]
QED
