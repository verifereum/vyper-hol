(* Request-prefix companion to bodyFullSubscriptMap. *)
Theory s1PrefixSubscriptMap
Ancestors
  s1PrefixPreds bodyFullSubscriptMap s1PrefixDefs

Theorem subscript_map_map_prefix:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_prefix_ok cx e2) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_map_pre cenv cx env (Subscript ann e1 e2) es /\
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es /\
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e1 es ==>
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  cheat
QED

Theorem subscript_map_prefix:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es kt vt.
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
  (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_prefix_ok cx e2) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
  place_type cenv e1 = MapPT kt vt /\
  expr_map_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e1 es /\
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e1 es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  cheat
QED
