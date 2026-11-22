(* Source exits without an expression record no request. *)
Theory s1PrefixExits
Ancestors
  s1PrefixFrame s1PrefixDefs vyperStorageTrace vyperInterpreter
  vyperState vyperAST list

Theorem compile_loop_jump_frag_prefix:
  (st = Break \/ st = Continue) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ty st)
    (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt st))
    (eval_stmt cx st) es
Proof
  strip_tac >>
  gvs[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, Once evaluate_def, raise_def]
QED

Theorem compile_raise_frag_prefix:
  (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Raise rk))
    (stmt_env (gas_shadow_env T cenv) lctx ty (gas_shadow_stmt (Raise rk)))
    (eval_stmt cx (Raise rk)) es
Proof
  strip_tac >>
  gvs[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, Once evaluate_def, raise_def]
QED
