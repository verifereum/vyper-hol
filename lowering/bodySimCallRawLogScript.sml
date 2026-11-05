(* Piece of bodySimCallCases.body_raw_log_case. *)

Theory bodySimCallRawLog
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* GAP (#636 operands with internal calls): raw_log.  Its case lemma is
   still stated over expr_sim_below, for compile_expr_sim only. *)
Theorem raw_log_body_expr_ok:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
Proof
  cheat
QED
