(* Request-prefix companion to bodyFullRaiseCustomError. *)
Theory s1PrefixRaiseCustomError
Ancestors
  s1PrefixPreds bodyFullRaiseCustomError s1PrefixDefs

Theorem compile_raise_custom_frag_prefix:
  !cx err DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
    env' ret_ty lctx RetQ es.
  (!id pos kw error_tops params args.
       err = CustomError id pos kw /\
       get_module_code cx (FST id) = SOME error_tops /\
       lookup_custom_error_args_in (SND id) error_tops = SOME params /\
       order_custom_error_args params err = SOME args ==>
       body_exprs_full_ok cx args) /\
  (!id pos kw error_tops params args.
       err = CustomError id pos kw /\
       get_module_code cx (FST id) = SOME error_tops /\
       lookup_custom_error_args_in (SND id) error_tops = SOME params /\
       order_custom_error_args params err = SOME args ==>
       body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Raise (RaiseCustomError err)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Raise (RaiseCustomError err)) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Raise (RaiseCustomError err))))
      (eval_stmt cx (Raise (RaiseCustomError err))) es
Proof
  cheat
QED
