Theory bodyPtrBopResidual
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list compileEnv

(* RESIDUAL: dynamic bytestring Eq/NotEq; held with S1's compile_bop_bytestring_eqne_case *)
Theorem bop_bytestring_expr_ptr_residual:
  !cx ty bop e1 e2.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH [e1;e2]) ==>
     body_exprs_ptr_ok cx [e1;e2]) /\
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1;e2])
Proof
  cheat
QED
