Theory extRetNoneFramePtr
Ancestors
  extRetCountedPtr bodyPtrDefs gasSummaryComposePtr loweringPosts
  vyperInterpreter vyperState stmtLowering compileEnv
  fragGasPathPtr gasSummary fragExec

Theorem external_return_none_stmt_frag_ptr:
  !cenv nkey ut iv cx env es ret_ty ctx PG func lctx.
    cenv.ce_return_pc = NONE /\ cenv.ce_ctor_exit_label = NONE /\
    cenv.ce_nonreentrant = (F,nkey,ut,iv) /\
    expr_sim_inv cenv cx env es /\ stmt_exprs_ok cenv (Return NONE) /\
    IS_SOME (type_stmt env ret_ty (Return NONE)) /\
    call_evaluation_safe cx (int_calls_stmt (Return NONE)) ==>
    stmt_frag_ptr NONE ctx PG func cx lctx (\v es gt r. T) cenv
      (stmt_env cenv lctx ret_ty (Return NONE))
      (eval_stmt cx (Return NONE)) es
Proof
  rpt gen_tac >> strip_tac >>
  rw[stmt_frag_ptr_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  `stor_taint_ok cx tn0 s0` by gvs[ghost_inv_def] >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 G0 tn0
     (Halt (halt_state (s0 with vs_returndata := [])))` by
    (irule compile_return_none_external_gas_path_ptr >> simp[] >>
     metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `G0`, `tn0`,
                `Halt (halt_state (s0 with vs_returndata := []))`] >>
  simp[gas_explicit_def, evaluate_def, raise_def, exit_result_def,
       stmt_exit_ptr_def]
QED
