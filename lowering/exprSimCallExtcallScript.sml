(*
 * The piece of exprSimCalls's compile_extcall_sim: extcall/staticcall in SOME oracle mode, reverts and default_return_value (#553).
 * extcall_expr_vv_ok is compile_extcall_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallExtcall
Ancestors
  list  exprSimHyps exprSimSend vyperAST

Theorem extcall_expr_vv_ok:
  !cenv ann is_static skip sig opts args dflt.
    expr_sim_below cenv (expr_size (Call ann (ExtCall is_static skip sig opts) args dflt)) ==>
    expr_vv_ok cenv (Call ann (ExtCall is_static skip sig opts) args dflt)
Proof
  cheat
QED
