(* Request-prefix companion to bodyFullBuiltinSliceOperands. *)
Theory s1PrefixBuiltinSliceOperands
Ancestors
  s1PrefixPreds bodyFullBuiltinSliceOperands s1PrefixDefs

Theorem slice_code_child_prefix:
  expr_body_pre cenv cx env
    (Builtin a (Slice n) [Builtin ct (Acc Code) [addr]; start; len]) es /\
  body_const_cells_agree [(NONE,tops)] cx env ee /\
  expr_sim_inv cenv cx env ee /\
  (e = start \/ e = len \/ e = addr) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e ee /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty e ee
Proof
  cheat
QED
