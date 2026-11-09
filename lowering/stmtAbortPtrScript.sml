(*
 * Pointer-checked aborts with no data: REVERT 0 0 and INVALID, and the
 * bare and unreachable raise, the twin of stmtSimRaise's compile_raise_frag
 * over stmt_frag_ptr.
 *
 * TOP-LEVEL:
 *   ptr_inst_ok_abort_zero    -- REVERT 0 0 and INVALID pass the check
 *   emit_abort_zero_path_ptr  -- such an emitted abort is a checked path
 *   compile_raise_frag_ptr    -- raise with no reason
 *)
Theory stmtAbortPtr
Ancestors
  bodyPtrDefs fragGasPathPtr gasCount stmtSimDefs stmtSimProps exprSimDefs loweringPosts
  fragExec stmtLowering compileEnv emitHelper emitHelperProps
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  vyperInterpreter vyperState venomInst venomState venomExecSemantics
Libs
  monadsyntax

(* REVERT 0 0 and INVALID read and write no memory and take no tainted
   operand, and their step aborts. *)
Theorem ptr_inst_ok_abort_zero:
  !D fuel ctx fn G tn s id opc ops.
    ((opc = REVERT /\ ops = [Lit 0w; Lit 0w]) \/ (opc = INVALID /\ ops = [])) /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops []) s
Proof
  rpt strip_tac >> gvs[]
  >- (qspecl_then [`id`, `s`] strip_assume_tac step_revert_zero >>
      gvs[mk_inst_def, ptr_inst_ok_def, step_inst_non_invoke] >>
      simp[access_ok_def, taint_ok_def, allocas_from_def, op_taint_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def,
           memory_range_of_operands_def, eval_operand_def,
           about_to_revert_def] >>
      metis_tac[op_taint_def]) >>
  qspecl_then [`id`, `s`] strip_assume_tac step_invalid >>
  gvs[mk_inst_def, ptr_inst_ok_def, step_inst_non_invoke] >>
  simp[access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def]
QED

(* emit_abort_zero_path with the pointer check: the ghost stays. *)
Theorem emit_abort_zero_path_ptr:
  emit_inst opc ops [] sa = ((), sb) /\ fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  opc <> INVOKE /\ opc <> GAS /\
  ptr_inst_ok D 0 0 ctx func G tn (mk_inst sa.cs_next_id opc ops []) s /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = Abort a t ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
       exit_result_def, ptr_safe_step_def] >>
  gvs[mk_inst_def]
QED

(* compile_raise_frag with the pointer check. *)
Theorem compile_raise_frag_ptr:
  !d ctx PG func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise rk)) (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def, Once evaluate_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `AssertException msg` >>
  qexistsl_tac [`INR (AssertException msg)`, `es`, `G0`, `tn0`] >>
  fs[markerTheory.Abbrev_def] >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s0 = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (simp[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G0 tn0 (Abort a t)` by
    (irule emit_abort_zero_path_ptr >> simp[] >>
     qexistsl_tac [`opc`, `ops`, `sa`, `sb`] >> simp[] >>
     irule ptr_inst_ok_abort_zero >> simp[]) >>
  qexists_tac `Abort a t` >> simp[exit_result_def, stmt_exit_ptr_def] >>
  gvs[]
QED

