(* Memory boundary facts for tuple assignment to existing locals. *)
Theory bodyMemAssignTupleLocalsFacts
Ancestors
  bodyDeclMemoryCore bodyDeclMemoryCounted stmtSimDefs compileEnv loweringStateRelDefs
  venomState valueEncoding finite_map list fragExec fragExecMem
  exprLoweringProps loweringSlice words

(* The backing region, not a subsequently executed ALLOCA, bounds a store.
   This is the local_ptrs_rel projection used in S3's
   bodyMemAssignLocalMem.local_memory_store_body_path. *)
Theorem tuple_local_destination_room:
  stmt_state_rel ctx func ce cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ n <= type_memory_size entry.type ==>
  local_backed func p s (w2n w) sz /\
  type_memory_size entry.type <= sz /\
  w2n w + n <= s.vs_alloca_next
Proof
  strip_tac >>
  `local_backed func p s (w2n w) sz /\
   w2n w + sz <= s.vs_alloca_next /\
   type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  simp[] >> decide_tac
QED

(* No premise says the staging site is fresh: the same interface covers
   both the first execution and loop re-entry with a cached allocation. *)
Theorem tuple_staging_memory_safe:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= n ==>
  ?a t w.
    run_inst_seq (emitted_insts sa sm) s = OK a /\
    run_inst_seq (emitted_insts sm sn) a = OK t /\
    run_inst_seq_mem_ok (emitted_insts sa sm) s /\
    run_inst_seq_mem_ok (emitted_insts sm sn) a /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    w2n w + n <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule_all body_scratch_prefix_run >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED
