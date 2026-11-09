(* Joint resource exit of a variable-only stack return. *)
Theory bodyIntCallFamStmtReturnStackExit
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtReturnStackRun
  bodyIntCallForcingReadOnly ctorReturnFrame compileEnv exprLoweringProps
  loweringPosts fragExec stmtSimReturn venomExecSemantics venomState

Theorem intcall_stack_exit_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  0 < fp.jc_root_ce.ce_returns_count /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  intret_vals_match fp.jc_ret_tv v ws /\
  LENGTH ws = fp.jc_root_ce.ce_returns_count ==>
  intcall_stmt_exit fp (INR (ReturnException v)) es
    (IntRet <|iret_values := ws; iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule forcing_readonly_state_rel >> qexistsl_tac [`t.vs_inst_idx`, `s`, `sa`] >>
     fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `state_rel fp.jc_func fp.jc_root_ce fp.jc_cx (es with scopes := []) t` by
    (irule constructor_exit_state_rel >> qexists_tac `ce` >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def, state_rel_gas_obs]) >>
  `fp.jc_rb = NONE` by
    (fs[intcall_frame_ok_def] >> Cases_on `fp.jc_rb` >> gvs[]) >>
  simp[intcall_stmt_exit_def] >> disj2_tac >>
  simp[intret_q_def, result_rel_def, state_rel_gas_obs] >>
  conj_tac
  >- (qpat_x_assum `t = _` SUBST1_TAC >> fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  rpt strip_tac >>
  `eval_operand op t = eval_operand op s` by
    (fs[intcall_frame_ok_def] >>
     first_x_assum drule >> strip_tac >> gvs[] >>
     simp[eval_operand_def] >> first_x_assum irule >>
     fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def]
QED
