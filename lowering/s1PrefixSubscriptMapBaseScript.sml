(* Request-prefix companion to bodyFullSubscriptMapBase. *)
Theory s1PrefixSubscriptMapBase
Ancestors
  s1PrefixPreds bodyFullSubscriptMapBase

Theorem body_expr_prefix_ok_map:
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_map_pre cenv cx env e es ==>
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  cheat
QED
