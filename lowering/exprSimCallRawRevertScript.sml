(*
 * The piece of exprSimCalls's compile_raw_revert_sim: raw_revert (#636).
 * raw_revert_expr_vv_ok is compile_raw_revert_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawRevert
Ancestors
  list  exprSimHyps exprSimSend vyperAST

Theorem raw_revert_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawRevert) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawRevert) args dflt)
Proof
  cheat
QED
