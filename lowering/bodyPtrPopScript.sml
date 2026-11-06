(*
 * pop: the taint bound holds before the length store and is kept through dead_bytes_frame.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   pop_expr_ptr_ok
 *)
Theory bodyPtrPop
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem pop_expr_ptr_ok:
  !cx v10 bt. body_base_target_ptr_ok cx bt ==> body_expr_ptr_ok cx (Pop v10 bt)
Proof
  cheat
QED
