(* Seam 2 joint induction, a family leaf of the stmt step: Return. *)
Theory bodyIntCallFamStmtReturn
Ancestors
  bodyIntCallJointContract bodyIntCallSharpReturn
  bodySim stmtSimReturn stmtSimDefs loweringPosts compileEnv ctorReturnFrame
  stmtLowering vyperTyping vyperInterpreter gasOutcome gasSummary
  gasSummaryCompose venomExecSemantics venomState

Theorem intcall_bare_return_producer:
  intcall_stmts_producer fp [Return NONE]
Proof
  simp[intcall_stmts_producer_def] >> rpt strip_tac >>
  `fp.jc_ret_ty = NoneT` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `ce.ce_return_pc = SOME (PtrVar fp.jc_rpc 0)` by
    fs[intcall_joint_res_def, intcall_frame_ok_def, same_frame_def,
       compile_env_component_equality] >>
  `emitHelper$emit_inst RET [fp.jc_rpc] [] sa = ((),sb)` by
    (qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
     simp[stmts_env_def, stmtLoweringTheory.declare_stmt_local_def,
          stmtLoweringTheory.compile_stmt_def, compileEnvTheory.comp_get_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_ignore_bind_def] >>
     Cases_on `emit_inst RET [fp.jc_rpc] [] sa` >>
     simp[]) >>
  `gas_path fp.jc_ctx fp.jc_func s 0
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s)` by
    (irule emitted_memory_ret_path >> conj_tac >- simp[] >>
     qexistsl_tac [`fp.jc_rpc`, `sa`, `sb`] >>
     fs[intcall_joint_res_def]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`,
    `IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def,
           fragGasModeTheory.gas_marked_path_def,
           vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.raise_def]) >>
  simp[fragExecTheory.exit_result_def, intcall_stmt_exit_def] >>
  disj2_tac >>
  fs[intcall_joint_res_def, intcall_frame_ok_def,
     returns_stack_count_def, vyperValueTheory.evaluate_type_def] >>
  simp[intret_q_def, result_rel_def] >>
  simp[intret_vals_match_def, state_rel_gas_obs] >>
  irule constructor_exit_state_rel >> qexists_tac `ce` >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_gas_obs]
QED

Theorem intcall_return_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?eo. st = Return eo) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED
