(* Piece of bodySimCallCases.body_raw_call_calldata_case. *)

Theory bodySimCallRawCallCalldata
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* GAP (#636 operands with internal calls): raw_call with calldata.  Its
   case lemma is still stated over expr_sim_below, for compile_expr_sim only. *)
Theorem raw_call_calldata_body_expr_ok:
  !cx ty flags es v19.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED
