(*
 * The piece of exprSimCalls's compile_raw_call_sim: raw_call (#554).
 * raw_call_expr_vv_ok is compile_raw_call_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawCall
Ancestors
  list  exprSimHyps exprSimSend vyperAST

Theorem raw_call_expr_vv_ok:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallTarget flags) args dflt)
Proof
  cheat
QED
