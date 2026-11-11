(* The root-frame exit after a memory-return store. *)
Theory bodyIntCallFamStmtReturnMemoryExit
Ancestors
  bodyIntCallJointContract stmtSimReturnWiden ctorReturnFrame
  exprLoweringProps loweringPosts compileEnv loweringStateRelDefs exprSimStorageCopy
  stmtSimReturn venomState venomExecSemantics vyperState bodySim

Theorem intcall_memory_exit_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  fp.jc_rb = SOME (bw,cap) /\ fp.jc_root_ce.ce_returns_count = 0 /\
  copy_static t = copy_static s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!off len. off + len <= w2n bw \/ w2n bw + cap <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!op. fp.jc_reserved op ==> eval_operand op t = eval_operand op s) /\
  val_in_memory fp.jc_ret_tv v (w2n bw) t.vs_memory ==>
  intcall_stmt_exit fp (INR (ReturnException v)) es
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t)
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
     (es with scopes := []) s` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def] >>
     conj_tac >- metis_tac[state_rel_scopes_nil] >>
     fs[immutable_alloca_sep_def, local_region_def, lookup_scopes_def] >>
     metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
     (es with scopes := []) t` by
    (irule typed_return_empty_state_frame >>
     qexistsl_tac [`w2n bw`, `s`, `cap`] >>
     simp[arithmeticTheory.ADD_COMM] >>
     reverse conj_tac >- (fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]) >>
     rpt strip_tac >>
     `eval_operand (Var x) t = eval_operand (Var x) s` by
       (first_x_assum irule >> fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def,
         same_frame_def, compile_env_component_equality]) >>
     fs[eval_operand_def]) >>
  `state_rel fp.jc_func fp.jc_root_ce fp.jc_cx
     (es with scopes := []) t` by
    (irule (SRULE [] (Q.INST [`es` |-> `es with scopes := []`]
       constructor_exit_state_rel)) >> qexists_tac `ce` >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def]) >>
  simp[intcall_stmt_exit_def] >> disj2_tac >>
  simp[intret_q_def, result_rel_def, intret_vals_match_def, state_rel_gas_obs] >>
  conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint a k (w2n bw) cap` by
        (fs[intcall_frame_ok_def] >> metis_tac[]) >>
      fs[regions_disjoint_def, intcall_joint_res_def, intcall_expr_res_def]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def]
QED
