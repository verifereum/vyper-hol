Theory s1PrefixStmtZero
Ancestors
  s1PrefixFrame s1PrefixDefs vyperStorageTrace vyperInterpreter
  vyperState vyperAST list

Theorem stmt_frag_nil_prefix:
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmts_env cenv lctx ty []) (stmts_env cenv lctx ty [])
    (eval_stmts cx []) es
Proof
  rw[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, Once evaluate_def, return_def]
QED

Theorem compile_pass_frag_prefix:
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ty Pass) (stmt_env cenv lctx ty Pass)
    (eval_stmt cx Pass) es
Proof
  rw[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, Once evaluate_def, return_def]
QED
