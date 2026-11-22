(* Request-prefix companion to bodyFullAssertCustomError. *)
Theory s1PrefixAssertCustomError
Ancestors
  s1PrefixPreds bodyFullAssertCustomError s1PrefixDefs

Theorem compile_assert_custom_frag_prefix_from_raise:
  !cx e err DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_stmt_full_ok cx (Raise (RaiseCustomError err))) /\
  (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_stmt_prefix_ok cx (Raise (RaiseCustomError err))) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assert e (AssertCustomError err)) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assert e (AssertCustomError err)) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertCustomError err)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Assert e (AssertCustomError err))))
      (eval_stmt cx (Assert e (AssertCustomError err))) es
Proof
  cheat
QED
