Theory bodyPtrTypeBuiltinsConvertEntry
Ancestors
  bodyPtrPreds exprSimHypsDefs vyperAST vyperTypeSystem

(* An ill-typed arity never enters either simulation judgment. *)
Theorem convert_arity_body_expr_ptr_ok:
  !cx ann typ args.
    LENGTH args <> 1 ==>
    body_expr_ptr_ok cx (TypeBuiltin ann Convert typ args)
Proof
  rw[body_expr_ptr_ok_def] >>
  fs[expr_body_pre_def, well_typed_expr_def,
     well_typed_type_builtin_args_def]
QED
