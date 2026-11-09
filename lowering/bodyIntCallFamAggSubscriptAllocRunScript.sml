(* Joint continuation at a supplied allocation execution endpoint. *)
Theory bodyIntCallFamAggSubscriptAllocRun
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointContract exprSimAlloc exprSimProps
  exprSimDefs exprSimCopy context compileEnv venomState instIdxIndep
  intCallFrame loweringPosts

Theorem intcall_alloc_run_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  sz < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  intcall_expr_cont fp ce env es sa s es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ?w. eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sa.cs_next_id < sb.cs_next_id /\
    (!name b len. local_region ce es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa` by fs[intcall_expr_res_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all intcall_joint_res_alloc >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  drule_all intcall_alloc_run_frame >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> simp[]) >>
  simp[intcall_expr_cont_frame, wb_frame_def, locals_kept_def,
       lookup_var_def, local_region_def] >>
  fs[venom_state_component_equality, local_region_def, lookup_var_def] >>
  metis_tac[]
QED
