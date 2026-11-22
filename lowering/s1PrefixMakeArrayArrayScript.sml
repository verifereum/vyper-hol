(* Request-prefix companion to bodyFullMakeArrayArray. *)
Theory s1PrefixMakeArrayArray
Ancestors
  s1PrefixPreds bodyFullMakeArrayArray s1PrefixDefs

Theorem make_array_vv_sim_prefix_conditional:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann et n args es.
  make_array_packaging_ok /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
       body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
       body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  cheat
QED
