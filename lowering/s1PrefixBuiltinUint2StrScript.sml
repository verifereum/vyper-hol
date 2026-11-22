(* Request-prefix companion to bodyFullBuiltinUint2Str. *)
Theory s1PrefixBuiltinUint2Str
Ancestors
  s1PrefixPreds bodyFullBuiltinUint2Str s1PrefixDefs

Theorem uint2str_builtin_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
     body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
     body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es /\
    expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Uint2Str n) args) es
Proof
  cheat
QED
