(* Request-prefix companion to bodyFullMakeTuple. *)
Theory s1PrefixMakeTuple
Ancestors
  s1PrefixPreds bodyFullMakeTuple s1PrefixDefs

Theorem make_tuple_vv_sim_prefix_conditional:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
  make_array_packaging_ok /\
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
      body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray NONE n) args) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray NONE n) args) es
Proof
  cheat
QED
