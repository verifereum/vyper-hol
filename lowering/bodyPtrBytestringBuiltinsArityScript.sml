Theory bodyPtrBytestringBuiltinsArity
Ancestors
  exprSimHypsDefs vyperTypeBuiltins

Theorem expr_body_pre_builtin_arity:
  !cenv cx env ann bt args es.
    expr_body_pre cenv cx env (Builtin ann bt args) es ==>
    builtin_args_length_ok bt (LENGTH args)
Proof
  rw[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  drule well_typed_builtin_app_length >> simp[]
QED
