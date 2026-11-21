Theory s1PrefixLiteralWord
Ancestors
  s1PrefixFrame s1PrefixDefs exprSimLiteralWord vyperStorageTrace
  vyperInterpreter vyperState vyperAST list

Theorem literal_word_value_prefix:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  rw[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, literal_read_all_tails]
QED

Theorem literal_vv_prefix:
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  rw[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, Once evaluate_def, return_def]
QED
