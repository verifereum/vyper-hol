(* RESIDUAL: held for membership checker repair (#742). *)
Theory bodyPtrBopInHeld
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim vyperAST compileEnv

val _ = Parse.hide "body";

Theorem bop_in_nonword_ptr_ok:
  !cx ty bop e1 e2.
    ~is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ptr_ok cx [e1; e2] ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  cheat
QED
