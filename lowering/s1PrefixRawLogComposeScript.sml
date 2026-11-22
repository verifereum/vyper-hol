(* Request-prefix companion to bodyFullRawLogCompose. *)
Theory s1PrefixRawLogCompose
Ancestors
  s1PrefixPreds bodyFullRawLogCompose s1PrefixDefs

Theorem raw_log_expr_sim_prefix:
  (!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))) /\
  (!ce xs. gas_shadow_compiles (compile_multi_exprs compile_expr ce xs)
    (compile_multi_exprs compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr xs))) /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann RawLog args dflt) es
Proof
  cheat
QED
