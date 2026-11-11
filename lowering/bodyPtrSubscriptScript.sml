(*
 * Subscripts: a storage place owes ptr_vv_ok's taint bound (storage_read_live, stor_taint_ok).
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   subscript_expr_ptr_ok
 *)
Theory bodyPtrSubscript
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem subscript_expr_ptr_ok:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 ==>
    body_expr_ptr_ok cx (Subscript v8 e1 e2)
Proof
  cheat
QED
