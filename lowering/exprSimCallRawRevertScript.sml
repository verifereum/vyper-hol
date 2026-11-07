(*
 * The piece of exprSimCalls's compile_raw_revert_sim: raw_revert (#636).
 * raw_revert_expr_vv_ok is compile_raw_revert_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawRevert
Ancestors
  list  exprSimHyps exprSimSend vyperAST
  exprSimRawRevertCore exprSimHypsDefs exprSimSource vyperTypeCallGraph

Theorem raw_revert_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawRevert) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawRevert) args dflt)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Call ann RawRevert args dflt) es /\
   int_calls_expr (Call ann RawRevert args dflt) = []` by
    metis_tac[expr_sim_pre_body] >>
  drule raw_revert_pre_arg >> strip_tac >> gvs[] >>
  irule raw_revert_vv_sim >>
  `expr_sim_pre cenv cx env e es` by
    gvs[expr_sim_pre_body, int_calls_expr_def] >>
  gvs[expr_sim_below_def] >>
  first_x_assum (qspec_then `e` mp_tac) >>
  simp[expr_size_def, expr_ok_def, expr_sim_ok_def] >> metis_tac[]
QED
