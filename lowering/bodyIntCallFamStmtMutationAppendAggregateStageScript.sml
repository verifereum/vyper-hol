(* Allocation-aware staging for aggregate Append operands. *)
Theory bodyIntCallFamStmtMutationAppendAggregateStage
Ancestors
  bodyIntCallFamStmtMutationStaging bodyIntCallJointContract context

Theorem intcall_append_aggregate_stage:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  type_memory_bytes ce elem = type_memory_size tv /\
  compile_alloc_buffer (type_memory_bytes ce elem) sa = (buf,sm) /\
  compile_store_memory ce raw buf.buf_operand elem elem sm = ((),sb) /\
  fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  type_memory_bytes ce elem < dimword (:256) /\
  eval_operand raw s = SOME sw /\ (!lbl. raw <> Label lbl) /\
  (!x. raw = Var x ==> not_fresh_at sa x) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es sa s es sb t /\
    intcall_joint_res fp ce env es sb t /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id =
      SOME (w2n w,type_memory_bytes ce elem) /\
    fp.jc_lo <= w2n w /\
    w2n w + type_memory_bytes ce elem < dimword (:256) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  `compile_copy_memory buf.buf_operand raw (type_memory_bytes ce elem) sm =
     ((),sb)` by gvs[compile_store_memory_def] >>
  `type_memory_size tv <= type_memory_bytes ce elem` by simp[] >>
  drule_all intcall_staging_initialize >> strip_tac >>
  qexistsl [`t`,`w`] >>
  fs[intcall_joint_res_def,intcall_expr_cont_def] >> metis_tac[]
QED
