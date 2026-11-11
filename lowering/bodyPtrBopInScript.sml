(*
 * in and not in, on array literals and on arrays.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   bop_in_expr_ptr_ok
 *)
Theory bodyPtrBopIn
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem bop_in_expr_ptr_ok:
  !cx ty bop es.
    (bop = In \/ bop = NotIn) /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) es)
Proof
  cheat
QED
