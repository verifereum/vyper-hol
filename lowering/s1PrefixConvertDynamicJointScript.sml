(* Request-prefix companion to bodyFullConvertDynamicJoint. *)
Theory s1PrefixConvertDynamicJoint
Ancestors
  s1PrefixPreds bodyFullConvertDynamicJoint s1PrefixDefs

Theorem convert_dynamic_vv_sim_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  cheat
QED
