(*
 * Attributes: a storage place owes ptr_vv_ok's taint bound.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   attribute_expr_ptr_ok
 *)
Theory bodyPtrAttribute
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem attribute_expr_ptr_ok:
  !cx v9 e id. body_expr_ptr_ok cx e ==> body_expr_ptr_ok cx (Attribute v9 e id)
Proof
  cheat
QED
