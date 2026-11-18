(* Counted actual-source simulation for bare and unreachable raise. *)
Theory stmtSimRaise
Ancestors
  stmtSimDefs stmtSimProps stmtSimAssertProps exprSimDefs loweringPosts gasOutcome gasSummary gasContext fragGasMode
  gasCount fragGasPath stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec list finite_map
Libs
  monadsyntax

Theorem compile_raise_frag:
  !ctx func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
       Once evaluate_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `AssertException msg` >>
  qexistsl_tac [`INR (AssertException msg)`, `es`] >>
  fs[markerTheory.Abbrev_def] >>
  `?a t. expr_exit (INR (AssertException msg) : unit + exception) (Abort a t) /\
         gas_path ctx func s0 0 (Abort a t)` by
    (qspecl_then [`opc`, `ops`, `msg`, `sa`, `sb`, `s0`, `func`, `ctx`] mp_tac
       abort_zero_exit >>
     impl_tac >- gvs[] >> simp[]) >>
  qexists_tac `Abort a t` >> simp[exit_result_def, stmt_exit_def] >>
  gvs[expr_exit_def, halt_exit_def]
QED

