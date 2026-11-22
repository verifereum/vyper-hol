(* Request-prefix companion to bodyFullHashKeccak. *)
Theory s1PrefixHashKeccak
Ancestors
  s1PrefixPreds bodyFullHashKeccak s1PrefixDefs

Theorem keccak_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann e es.
  expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  cheat
QED
