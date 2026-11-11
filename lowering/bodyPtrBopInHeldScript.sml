(* A membership needle of non-word type is ill-typed (the checker admits only
   flag and word needles), so expr_body_pre rules the case out. *)
Theory bodyPtrBopInHeld
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim vyperAST compileEnv exprSimHypsDefs
  vyperTypeSystem

val _ = Parse.hide "body";

Theorem bop_in_nonword_ptr_ok:
  !cx ty bop e1 e2.
    ~is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ptr_ok cx [e1; e2] ==>
    body_expr_ptr_ok cx (Builtin ty (Bop bop) [e1; e2])
Proof
  rpt strip_tac >> simp[Once body_expr_ptr_ok_def] >> rpt strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
      well_typed_binop_def, membership_element_word_boundary, is_word_type_def]
QED
