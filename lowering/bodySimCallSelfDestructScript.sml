(* Piece of bodySimCallCases.body_selfdestruct_case. *)

Theory bodySimCallSelfDestruct
Ancestors
  bodySimExprCases
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph

(* GAP (#636 operands with internal calls): selfdestruct.  Its case lemma is
   still stated over expr_sim_below, for compile_expr_sim only. *)
Theorem selfdestruct_body_expr_ok:
  !cx v24 es v25.
    body_exprs_ok cx es ==>
    body_expr_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  cheat
QED
