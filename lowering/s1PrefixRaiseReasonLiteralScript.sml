(* Raising with a literal string leaves the source trace unchanged. *)
Theory s1PrefixRaiseReasonLiteral
Ancestors
  s1PrefixFrame s1PrefixDefs reasonSourceProps
  vyperStorageTrace vyperState vyperAST list

Theorem compile_raise_reason_literal_frag_prefix:
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty
      (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))))
    (eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  rw[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, eval_raise_string_literal_reason]
QED
