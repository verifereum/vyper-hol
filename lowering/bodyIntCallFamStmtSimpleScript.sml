(* Seam 2 joint induction, a family leaf of the stmt step: Pass, Break, Continue and expression statements. *)
Theory bodyIntCallFamStmtSimple
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtZero bodyIntCallJointStmtExpr
  bodyIntCallJointStmtJump bodyIntCallJointStmtBoundary bodyIntCallJointStmtSeq stmtSimForRounds
  stmtSimProps stmtSimDefs loweringPosts stmtLowering compileEnv emitHelper
  emitHelperProps exprLoweringProps exprSimWordArgs exprSimHypsDefs
  vyperInterpreter vyperState vyperTypeSystem gasOutcome gasSummary
  gasContext fragGasMode fragGasPath fragExec venomState venomExecSemantics
  bodyMemoryDefs list finite_map

Theorem intcall_joint_res_gas_obs:
  intcall_joint_res fp ce env (es with gas_obs := gs) sa s <=>
  intcall_joint_res fp ce env es sa s
Proof
  simp[intcall_joint_res_def, stmt_state_rel_gas_obs]
QED

Theorem intcall_stmts_producer_loop_jump:
  !fp st. (st = Break \/ st = Continue) ==> intcall_stmts_producer fp [st]
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lctx` >>
  gvs[gas_admissible_def, stmt_res_ok_def, Once evaluate_def, raise_def] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       comp_ignore_bind_def, comp_bind_def, compile_stmt_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  rename1 `emit_inst JMP [Label dest] [] sa = ((),sj)` >>
  qmatch_goalsub_abbrev_tac `gas_marked_exec _ _ source` >>
  qexistsl_tac [`FST (source es)`, `es`, `OK (jump_to dest s)`] >>
  simp[Abbr `source`, evaluate_def, raise_def] >>
  (conj_tac >- (simp[gas_marked_exec_def, gas_marked_path_def, evaluate_def,
                    raise_def] >> irule emit_jump_zero_path >> simp[] >>
               qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  qexistsl_tac [`ce`, `env`] >>
  simp[stmt_lands_def, cenv_top_ext_refl, jump_to_def, lookup_var_def,
       intcall_joint_res_jump_to, intcall_joint_res_gas_obs] >>
  irule intcall_joint_res_next_var >> goal_assum (drule_at Any) >> simp[])
QED

Theorem intcall_simple_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (st = Pass \/ st = Break \/ st = Continue \/ ?e. st = Expr e) ==>
  intcall_stmts_producer fp [st]
Proof
  metis_tac[intcall_stmts_producer_expr, intcall_stmts_producer_loop_jump,
            intcall_stmts_producer_pass]
QED
