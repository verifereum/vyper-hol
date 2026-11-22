(* A return without a value has no source request. *)
Theory s1PrefixReturnNone
Ancestors
  s1PrefixFrame s1PrefixDefs vyperStorageTrace vyperInterpreter
  vyperState vyperTypeSystem vyperAST list option

Theorem compile_return_none_frag_prefix:
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Return NONE))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  rw[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame, Once evaluate_def, raise_def]
QED

Theorem frame_ret_none_prefix:
  frame_ret_ok_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv NoneT
Proof
  simp_tac std_ss [frame_ret_ok_prefix_def, frame_ret_ok_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `eo` >> gvs[type_stmt_def, compile_return_none_frag_prefix]
QED
