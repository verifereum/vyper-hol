Theory s1PrefixStmtFullApply
Ancestors
  bodyFullPreds

Theorem body_stmt_full_ok_apply:
  !cx s. body_stmt_full_ok cx s ==>
    !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
       env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      supported_stmt tops bindings s /\
      (!target. supported_stmt_expr_exists
         (expr_abi_decode_target_root target) s ==>
         occurs_abi_decode_target target tops) /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s)
        (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt s))
        (eval_stmt cx s) es
Proof
  pure_rewrite_tac[body_stmt_full_ok_def] >> simp[]
QED

Theorem body_stmts_full_ok_apply:
  !cx ss. body_stmts_full_ok cx ss ==>
    !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
       env' ret_ty lctx RetQ es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      supported_stmts tops bindings ss /\
      (!target. supported_stmts_expr_exists
         (expr_abi_decode_target_root target) ss ==>
         occurs_abi_decode_target target tops) /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      stmts_exprs_ok cenv ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss)
        (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
        (eval_stmts cx ss) es
Proof
  pure_rewrite_tac[body_stmts_full_ok_def] >> simp[]
QED
