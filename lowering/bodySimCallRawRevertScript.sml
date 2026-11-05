(* Piece of bodySimCallCases.body_raw_revert_case. *)

Theory bodySimCallRawRevert
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* GAP (#636 operands with internal calls): raw_revert.  Its case lemma is
   still stated over expr_sim_below, for compile_expr_sim only. *)
Theorem raw_revert_body_expr_ok:
  !cx v22 es v23.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v22 RawRevert es v23)
Proof
  cheat
QED
