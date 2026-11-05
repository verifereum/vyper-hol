(*
 * The piece of exprSimCalls's compile_raw_call_calldata_sim: raw_call of msg.data (#554).
 * raw_call_calldata_expr_vv_ok is compile_raw_call_calldata_sim's statement; exprSimCalls takes it as is.
 *)

Theory exprSimCallRawCallCalldata
Ancestors
  list exprSimHyps exprSimSend exprSimRawCallCalldata vyperAST

Theorem raw_call_calldata_expr_vv_ok:
  !cenv ann flags args dflt.
    expr_sim_below cenv (expr_size (Call ann (RawCallCalldataTarget flags) args dflt)) ==>
    expr_vv_ok cenv (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  `exprs_case T ctx func cenv cx args` by
    (irule exprs_case_below >> irule expr_sim_below_mono >>
     goal_assum (drule_at Any) >> simp[expr_size_def]) >>
  metis_tac[compile_raw_call_calldata_case]
QED
