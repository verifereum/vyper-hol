(*
 * The piece of exprSimCalls's compile_raw_call_calldata_sim: raw_call of msg.data (#554).
 * raw_call_calldata_expr_vv_ok is compile_raw_call_calldata_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawCallCalldata
Ancestors
  list  exprSimHyps exprSimSend vyperAST

Theorem raw_call_calldata_expr_vv_ok:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallCalldataTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  cheat
QED
