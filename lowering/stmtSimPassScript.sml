(* A source pass and an empty list compile to the same counted fragment. *)
Theory stmtSimPass
Ancestors
  stmtSimDefs stmtSimZero loweringPosts stmtLowering emitHelper
  compileEnv vyperInterpreter vyperState

Theorem compile_pass_frag:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass)
      (eval_stmt cx Pass) es
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `stmt_env cenv lctx ty Pass = stmts_env cenv lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  simp[stmt_frag_nil]
QED

Theorem compile_pass_frag_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass)
      (eval_stmt cx Pass) es
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `stmt_env cenv lctx ty Pass = stmts_env cenv lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  simp[stmt_frag_nil_mem]
QED

Theorem compile_pass_frag_full:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty es.
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty Pass) (stmt_env cenv lctx ty Pass)
      (eval_stmt cx Pass) es
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `stmt_env cenv lctx ty Pass = stmts_env cenv lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  simp[stmt_frag_nil_full]
QED
