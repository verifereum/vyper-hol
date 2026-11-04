(* Counted memory-safe bare and unreachable raises. *)
Theory stmtRaiseMemory
Ancestors
  stmtSimDefs stmtSimProps stmtSimRaise exprSimDefs loweringPosts
  gasOutcome gasSummary gasContext fragGasMode gasCount fragGasPathMem
  stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec instMemFrontier list finite_map
Libs
  monadsyntax

(* Previous successful fixed-result proof (retained verbatim):
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule emit_abort_exit_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `s0`, `RetQ`, `es'`, `res`] mp_tac) >>
  (impl_tac
   >- (fs[markerTheory.Abbrev_def] >>
       qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, raise_def] >> strip_tac >>
       gvs[expr_exit_def, control_abort_frontier] >>
       metis_tac[step_revert_zero_mem, step_invalid_mem])) >>
  metis_tac[]
QED
*)
Theorem compile_raise_frag_mem:
  !d ctx func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
       Once evaluate_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `AssertException msg` >>
  qexistsl_tac [`INR (AssertException msg)`, `es`] >>
  fs[markerTheory.Abbrev_def] >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s0 = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (simp[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid]) >>
  qexists_tac `Abort a t` >> simp[exit_result_def, stmt_exit_def] >>
  (conj_tac >- (irule emit_abort_zero_path_mem >> simp[] >>
     qexistsl_tac [`opc`, `ops`, `sa`, `sb`] >> simp[] >>
     gvs[] >> simp[below_frontier_REVERT, eval_operand_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
   gvs[expr_exit_def])
QED

