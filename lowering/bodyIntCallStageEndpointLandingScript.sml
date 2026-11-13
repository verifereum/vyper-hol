(* Expression-resource allocation and forcing boundaries for argument staging. *)
Theory bodyIntCallStageEndpointLanding
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointForce bodyIntCallWindowLanding
  bodyIntCallJointContract
  exprSimProps exprSimCopy exprLoweringProps freshWrites

Theorem intcall_stage_allocation_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  sa.cs_next_var <= sb.cs_next_var /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_above fp.jc_lo u /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
    local_region ce es.scopes s name b sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >>
     `?x w. op = Var x /\ lookup_var x fp.jc_oorig = SOME w` by
       metis_tac[intcall_frame_ok_def] >>
     gvs[venomStateTheory.eval_operand_def] >>
     `not_fresh_at sa x` by metis_tac[intcall_expr_res_def] >> simp[]) >>
  `intcall_expr_res fp ce env es sb u` by
    (irule bodyIntCallJointAggCoreTheory.intcall_joint_res_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[intcall_expr_cont_def] >>
  irule exprSimPropsTheory.locals_kept_mem >> simp[]
QED

Theorem intcall_stage_expr_alloc_landing:
  compile_alloc_buffer sz sa = (buf,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env es sa s es sb u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    fp.jc_lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    u.vs_memory = s.vs_memory /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\
    sa.cs_next_id < sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op u = eval_operand op s) /\
    (!name b len. local_region ce es.scopes u name b len <=>
      local_region ce es.scopes s name b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sb p)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s /\
   local_ptrs_reserved ce sa /\ allocas_above fp.jc_lo s /\
   (!q x. fp.jc_reserved q /\ q = Var x ==> not_fresh_at sa x)` by
    fs[intcall_expr_res_def] >>
  drule_all (SRULE [] (Q.INST
    [`reserved` |-> `\q. !x. q = Var x ==> not_fresh_at sa x`]
    bodyIntCallWindowLandingTheory.materialization_alloc_landing)) >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id < sb.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!name b len. local_region ce es.scopes u name b len <=>
    local_region ce es.scopes s name b len` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  `intcall_expr_cont fp ce env es sa s es sb u` by
    (irule intcall_stage_allocation_cont >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >>
  simp[venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def] >> metis_tac[]
QED
