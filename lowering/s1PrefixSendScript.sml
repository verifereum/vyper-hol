(* Request-prefix companion to bodyFullSend. *)
Theory s1PrefixSend
Ancestors
  s1PrefixPreds bodyFullSend s1PrefixDefs

Theorem send_expr_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  cheat
QED

Theorem send_expr_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  cheat
QED

Theorem body_send_case_prefix:
  !cx v12 has_gas es v13.
  (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Call v12 (Send has_gas) es v13)
Proof
  cheat
QED
