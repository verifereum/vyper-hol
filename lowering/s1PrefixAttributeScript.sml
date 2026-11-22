(* Request-prefix companion to bodyFullAttribute. *)
Theory s1PrefixAttribute
Ancestors
  s1PrefixPreds bodyFullAttribute s1PrefixDefs

Theorem attribute_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj fld es.
  expr_body_pre cenv cx env (Attribute ann obj fld) es /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es /\
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty obj es ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Attribute ann obj fld) es
Proof
  cheat
QED

Theorem attribute_expr_prefix_ok:
  !cx v9 e id.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e ==>
  body_expr_prefix_ok cx (Attribute v9 e id)
Proof
  cheat
QED
