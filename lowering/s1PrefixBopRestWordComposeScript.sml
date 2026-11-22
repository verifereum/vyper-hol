(* Request-prefix companion to bodyFullBopRestWordCompose. *)
Theory s1PrefixBopRestWordCompose
Ancestors
  s1PrefixPreds bodyFullBopRestWordCompose s1PrefixDefs

Theorem compile_rest_word_membership_prefix:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop e1 e2 bd es.
  (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_full_ok cx [e1;e2] /\
  body_exprs_prefix_ok cx [e1;e2] /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  cheat
QED
