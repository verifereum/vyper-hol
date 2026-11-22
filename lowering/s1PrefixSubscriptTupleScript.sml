(* Request-prefix companion to bodyFullSubscriptTuple. *)
Theory s1PrefixSubscriptTuple
Ancestors
  s1PrefixPreds bodyFullSubscriptTuple s1PrefixDefs

Theorem subscript_tuple_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann obj idx es tys.
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\
  place_type cenv obj = ValPT (TupleT tys) /\
  post_value_type cenv obj = expr_type obj /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  cheat
QED
