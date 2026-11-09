(* Storage mutations preserve joint resources through defined old operands. *)
Theory bodyIntCallFamStmtMutationResourceLanding
Ancestors
  bodyIntCallJointContract bodyMemoryDefs stmtSimProps exprSimProps
  compileEnv exprLoweringProps venomState intCallFrame

Theorem intcall_joint_res_storage_landing:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee u /\
  expr_sim_inv ce fp.jc_cx env' ee /\
  ce_locals_declared ce env' /\ locals_alloc_ok ce env' /\
  local_ptrs_reserved ce sb /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  ee.immutables = es.immutables /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next ==>
  intcall_joint_res fp ce env' ee sb u
Proof
  pure_rewrite_tac[intcall_joint_res_def, intcall_expr_res_def] >> strip_tac >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >>
     fs[intcall_frame_ok_def] >>
     qpat_x_assum `!op. fp.jc_reserved op ==> ?x w. _`
       (qspec_then `op` mp_tac) >>
     simp[] >> strip_tac >> gvs[eval_operand_def] >>
     qpat_x_assum `!op. fp.jc_reserved op ==> eval_operand op s = _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def] >> strip_tac >>
     qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` irule >>
     simp[]) >>
  rpt conj_tac >> simp[allocas_above_def]
  >- (fs[allocas_above_def] >> metis_tac[])
  >- (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (rpt strip_tac >>
      `local_region ce es.scopes s n p k` by
        (irule local_region_frame >>
         fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
      metis_tac[arithmeticTheory.ADD_COMM])
  >- (fs[intcall_frame_ok_def] >> metis_tac[])
  >- (irule ret_pc_ok_frame >> metis_tac[])
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  metis_tac[]
QED
