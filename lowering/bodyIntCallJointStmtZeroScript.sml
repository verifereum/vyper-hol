(* Full joint producer boundaries for statements that emit no code. *)
Theory bodyIntCallJointStmtZero
Ancestors
  bodyIntCallJointContract stmtSimForRounds stmtSimZero loweringPosts
  stmtLowering emitHelper compileEnv vyperInterpreter vyperState fragGasMode
  fragGasPath stmtSimProps

Theorem intcall_stmts_producer_nil:
  !fp. intcall_stmts_producer fp []
Proof
  simp[intcall_stmts_producer_def, stmts_env_def, comp_return_def,
       vyperTypeSystemTheory.type_stmt_def, evaluate_def] >>
  rpt strip_tac >> irule gas_outcome_return_path >>
  qexists_tac `s` >> simp[gas_marked_path_def, gas_path_rules] >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  fs[intcall_joint_res_def, intcall_expr_res_def] >>
  metis_tac[]
QED

Theorem intcall_stmts_producer_pass:
  !fp. intcall_stmts_producer fp [Pass]
Proof
  simp[intcall_stmts_producer_def, stmts_env_def, declare_stmt_local_def,
       compile_stmt_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, comp_get_def, vyperTypeSystemTheory.type_stmt_def,
       evaluate_def, bind_def, return_def] >>
  rpt strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      vyperStateTheory.bind_return, vyperStateTheory.ignore_bind_def] >>
  irule gas_outcome_return_path >>
  qexists_tac `s` >> simp[gas_marked_path_def, gas_path_rules] >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  fs[intcall_joint_res_def, intcall_expr_res_def] >> metis_tac[]
QED
