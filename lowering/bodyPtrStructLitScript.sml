(*
 * Struct literals.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   structlit_expr_ptr_ok
 *)
Theory bodyPtrStructLit
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem structlit_expr_ptr_ok:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_ptr_ok cx (MAP SND kes)) ==>
    body_expr_ptr_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  cheat
QED
