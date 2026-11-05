(*
 * The piece of exprSimCalls's compile_raw_log_sim: raw_log (#636).
 * raw_log_expr_vv_ok is compile_raw_log_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawLog
Ancestors
  list  exprSimHyps exprSimSend vyperAST

Theorem raw_log_expr_vv_ok:
  !cenv ann args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawLog) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawLog) args dflt)
Proof
  cheat
QED
