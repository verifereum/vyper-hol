(* Bare raises leave through the abort alternative, with no resource endpoint. *)
Theory bodyIntCallJointStmtRaise
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtSeq stmtSimProps loweringPosts
  gasOutcome gasSummary gasContext fragGasMode fragGasPath stmtLowering
  compileEnv emitHelper emitHelperProps exprSimDefs fragExec
  exprLoweringProps vyperInterpreter vyperState
  venomInst venomState venomExecSemantics venomExecProofs

Theorem intcall_stmts_producer_raise:
  !fp rk. (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    intcall_stmts_producer fp [Raise rk]
Proof
  rpt gen_tac >> strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
       Once evaluate_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `AssertException msg` >>
  qexistsl_tac [`INR (AssertException msg)`, `es`] >>
  fs[markerTheory.Abbrev_def] >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (simp[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid]) >>
  qexists_tac `Abort a t` >> simp[exit_result_def, intcall_stmt_exit_def] >>
  gvs[] >> irule emit_abort_zero_path >> simp[]
  >~ [`emit_inst REVERT _ _ _ = _`]
    >- (qexistsl_tac [`REVERT`, `[Lit 0w; Lit 0w]`, `sa`, `sb`] >> simp[]) >>
  qexistsl_tac [`INVALID`, `[]`, `sa`, `sb`] >> simp[]
QED
