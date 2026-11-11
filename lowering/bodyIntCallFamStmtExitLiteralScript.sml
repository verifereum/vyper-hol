(* Literal reason Raise: zero-mark abort with no resource endpoint. *)
Theory bodyIntCallFamStmtExitLiteral
Ancestors
  stmtSimReason bodyIntCallJointContract bodyIntCallJointStmtSeq
  stmtSimProps stmtLowering exprLowering emitHelper compileEnv
  gasOutcome gasSummary gasContext loweringPosts vyperInterpreter vyperState

Theorem intcall_stmts_producer_raise_literal:
  intcall_stmts_producer fp
    [Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))]
Proof
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, compile_reason_message_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `compile_bytelike_literal _ _ sa = (buf,sm)` >>
  strip_tac >> gvs[] >>
  `~is_word_type (BaseT (StringT (STRLEN str)))` by simp[is_word_type_def] >>
  drule_all compile_bytelike_revert_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def,
       Once evaluate_def, raise_def] >>
  qexistsl_tac [`INR (AssertException str)`, `es`, `Abort Revert_abort t`] >>
  simp[Once evaluate_def, vyperValueOperationTheory.evaluate_literal_def, read_result_def, bind_def,
       lift_option_type_def, vyperValueTheory.dest_StringV_def, return_def, raise_def,
       fragExecTheory.exit_result_def, intcall_stmt_exit_def,
       exprSimDefsTheory.expr_exit_def]
QED
