(* Readonly normal endpoints, including the word-binop prefix. *)
Theory bodyIntCallFamStmtMutationBinop
Ancestors
  bodyIntCallJointContract bodyIntCallJointPurePath exprSimProps stmtSimProps
  intCallFrame compileEnv exprLoweringProps venomState bodyMemoryDefs

Theorem intcall_expr_cont_readonly_path:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  gas_marked_path memory fp.jc_ctx fp.jc_func s n (OK u) /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es u /\
  local_ptrs_reserved ce sb /\ sa.cs_next_var <= sb.cs_next_var /\
  u.vs_memory = s.vs_memory /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
         lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >>
  `allocas_above fp.jc_lo u` by
    (irule gas_marked_path_allocas_above >>
     fs[intcall_expr_res_def] >> metis_tac[]) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    metis_tac[gas_marked_path_alloca_next_mono] >>
  `!op. fp.jc_reserved op ==> eval_operand op u = eval_operand op s` by
    (rpt strip_tac >>
     fs[intcall_frame_ok_def] >>
     qpat_x_assum `!op. fp.jc_reserved op ==> ?x w. _`
       (qspec_then `op` mp_tac) >>
     simp[] >> strip_tac >> gvs[eval_operand_def] >>
     fs[intcall_expr_res_def] >>
     qpat_x_assum `!op. fp.jc_reserved op ==> eval_operand op s = _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def] >> metis_tac[]) >>
  simp[intcall_expr_cont_def] >>
  reverse conj_tac >- (irule locals_kept_mem >> simp[]) >>
  pure_rewrite_tac[intcall_expr_res_def] >>
  fs[intcall_expr_res_def] >> rpt conj_tac >> simp[]
  >- (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (rpt strip_tac >>
      `local_region ce es.scopes s n' p k` by
        (irule local_region_frame >>
         fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
      metis_tac[])
  >- (fs[intcall_frame_ok_def] >> metis_tac[])
  >- (irule ret_pc_ok_frame >> metis_tac[])
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  metis_tac[]
QED
