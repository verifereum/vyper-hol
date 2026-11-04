(* Counted memory-safe direct loop control, preserving caller buffers. *)
Theory stmtSimJumpMem
Ancestors
  stmtSimDefs stmtSimProps stmtSimBreak stmtSimContinue bodyMemoryDefs
  loweringPosts gasOutcome gasSummary fragGasMode fragGasPathMem
  stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomState
  venomExecSemantics fragExec allocaHistory list finite_map

Theorem compile_break_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break)
      (eval_stmt cx Break) es
Proof
  rw[stmt_frag_mem_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
       comp_bind_def, compile_stmt_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR BreakException`, `es`, `OK (jump_to ex s0)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           raise_def] >> irule emit_jump_zero_path_mem >> simp[] >>
      qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  `stmt_post ctx func cx (InLoop ex inc) cenv cenv sa sj s0
     (INR BreakException) (es with gas_obs := []) (jump_to ex s0)` by
    (irule stmt_post_break >> simp[]) >>
  gvs[stmt_post_def] >>
  rename1 `cenv_top_ext cenv c es.scopes` >> qexists_tac `c` >> simp[] >>
  conj_tac
  >- (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
      fs[cenv_top_ext_def, compile_env_component_equality]) >>
  fs[alloca_history_def, jump_to_def]
QED

Theorem compile_continue_frag_mem:
  !d ctx func cx RetQ cenv ty ex inc es.
    stmt_frag_mem d ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue)
      (eval_stmt cx Continue) es
Proof
  rw[stmt_frag_mem_def, stmt_env_def,
     declare_stmt_local_def, comp_bind_def, comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR ContinueException`, `es`, `OK (jump_to inc s0)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           raise_def] >> irule emit_jump_zero_path_mem >> simp[] >>
      qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  `stmt_post ctx func cx (InLoop ex inc) cenv cenv sa sj s0
     (INR ContinueException) (es with gas_obs := []) (jump_to inc s0)` by
    (irule continue_jump_post >> simp[]) >>
  gvs[stmt_post_def] >>
  rename1 `cenv_top_ext cenv c es.scopes` >> qexists_tac `c` >> simp[] >>
  conj_tac
  >- (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
      qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
      fs[cenv_top_ext_def, compile_env_component_equality]) >>
  fs[alloca_history_def, jump_to_def]
QED

