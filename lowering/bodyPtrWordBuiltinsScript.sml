(*
 * Word arithmetic builtins.
 * A piece of bodyPtrExprCases: the pointer twin of S1's case
 * (bodySimExprCases), over bodyPtrPreds's predicates.
 *
 * TOP-LEVEL:
 *   word_builtin_expr_ptr_ok
 *)
Theory bodyPtrWordBuiltins
Ancestors
  bodyPtrWordBuiltinsUnaryCases bodyPtrWordBuiltinsRemainingCases
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem word_builtin_expr_ptr_ok:
  !cx ty bt es.
    (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Builtin ty bt es)
Proof
  metis_tac[body_word_unary_ptr_ok, body_word_remaining_ptr_ok]
QED
