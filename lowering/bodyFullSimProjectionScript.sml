Theory bodyFullSimProjection
Ancestors bodyFullPreds

Theorem body_expr_full_ok_simulations:
  body_expr_full_ok cx e /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
  metis_tac[]
QED
