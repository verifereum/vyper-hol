(* Request-prefix companion to bodyFullHash. *)
Theory s1PrefixHash
Ancestors
  s1PrefixPreds bodyFullHash s1PrefixDefs

Theorem hash_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann bt e es.
  (bt = Keccak256 \/ bt = Sha256) /\
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann bt [e]) es
Proof
  cheat
QED

Theorem hash_expr_prefix_ok:
  !cx ty bt es.
  (bt = Keccak256 \/ bt = Sha256) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) /\
  (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Builtin ty bt es)
Proof
  cheat
QED
