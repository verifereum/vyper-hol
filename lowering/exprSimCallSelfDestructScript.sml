(*
 * The piece of exprSimCalls's compile_selfdestruct_sim: selfdestruct (#636).
 * selfdestruct_expr_vv_ok is compile_selfdestruct_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallSelfDestruct
Ancestors
  list  exprSimHyps exprSimSend vyperAST

Theorem selfdestruct_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (SelfDestructTarget) args dflt)) ==>
    expr_vv_ok cenv (Call ann (SelfDestructTarget) args dflt)
Proof
  cheat
QED
