(* Counted actual-source simulation for bare and unreachable raise. *)
Theory stmtSimRaise
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasContext fragGasMode
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
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_abort_exit >>
  disch_then (qspecl_then [`ctx`, `func`, `s0`, `RetQ`, `es'`, `res`]
                mp_tac) >>
  (impl_tac
   >- (fs[markerTheory.Abbrev_def] >>
       qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, raise_def] >> strip_tac >>
       gvs[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid])) >>
  metis_tac[]
QED
