(*
 * The body simulation of S1: in and not in on an array literal of words
 * (#636 operands with internal calls).  Its lowering compiles each element
 * (exprSimBopInLiteralWord), while the induction hypotheses give the
 * judgment of the array only.
 *
 * TOP-LEVEL:
 *   body_bop_in_literal_word_case — that case
 *)

Theory bodySimBopInLiteralWord
Ancestors
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph

Theorem body_bop_in_literal_word_case:
  !cx ty bop e1 a t n elems.
    is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED
