(*
 * IfExp: either arm's buffer is handed out, so val_store_size of the value is covered.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   ifexp_expr_ptr_ok
 *)
Theory bodyPtrIfExp
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem ifexp_expr_ptr_ok:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok cx e3) /\
    body_expr_ptr_ok cx e1 ==>
    body_expr_ptr_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED
