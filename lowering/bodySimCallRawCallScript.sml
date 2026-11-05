(* Piece of bodySimCallCases.body_raw_call_case. *)

Theory bodySimCallRawCall
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* GAP (#636 operands with internal calls): raw_call.  Its case lemma is
   still stated over expr_sim_below, for compile_expr_sim only. *)
Theorem raw_call_body_expr_ok:
  !cx ty flags es v18.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  cheat
QED
