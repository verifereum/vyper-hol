(*
 * The body simulation of S1: in and not in on an array literal of words
 * (#636 operands with internal calls).  Its lowering compiles each element
 * (exprSimBopInLiteralWord), so this takes the elements' judgments.  The
 * induction hypotheses give the array's only; bodySimBopHeld's
 * body_make_array_children_ok extracts the elements' from it.
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
    (bop = In \/ bop = NotIn) /\ body_expr_ok cx e1 /\
    ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                       read_result cx tv s1 = (INL v, t1)) ==>
     builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
     body_exprs_ok cx elems) ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED
