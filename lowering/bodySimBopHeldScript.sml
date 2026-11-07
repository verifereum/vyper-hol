(* The source type checker excludes literal membership on non-word operands. *)

Theory bodySimBopHeld
Ancestors
  bodySim exprSimHypsDefs vyperTypeSystem compileEnv

Theorem body_bop_in_literal_nonword_case:
  !cx ty bop e1 a t n elems.
    ~is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once body_expr_ok_def, expr_body_pre_def] >>
  rpt strip_tac >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >>
  gvs[well_typed_binop_def, GSYM membership_element_word_boundary,
      is_prim_word_type_def]
QED
