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

Theorem compile_raise_frag_mem:
  !d ctx func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
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

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag compile_raise_frag_mem)
  in if null axioms andalso null (Thm.hyp compile_raise_frag_mem) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "RAISE_MEMORY_KERNEL_AUDIT OK\n"
     else raise Fail "raise memory inherited admission"
  end;
