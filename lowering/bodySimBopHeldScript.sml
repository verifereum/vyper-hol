(*
 * The body simulation of S1: in and not in on an array literal, the parts
 * not provable at the base.
 *
 * body_bop_in_literal_nonword_case:
 * HELD for #742: false at base 18f70e04a, as exprSimBopHeld's
 * compile_bop_in_literal_nonword_sim: the lowering compares each element's
 * word, the source compares the values.  This admission is owned by the
 * round that brings #742 (vyper-hol PR #742, integration copy #1092) in
 * after the sixteen frozen branches merge; it is not open work here.
 *
 * TOP-LEVEL:
 *   body_bop_in_literal_nonword_case — in and not in on a literal of
 *                              non-words
 *)

Theory bodySimBopHeld
Ancestors
  exprSimSource
  exprSimHypsDefs
  list bodySim  exprSimHyps exprSimOperators exprSimAttribute
  exprSimPlaces exprSimPopNested targetPlaceSim exprSimAggregates exprSimSend exprSimMain exprSimECArith vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph vyperTypeSystem compileEnv

Theorem body_bop_in_literal_nonword_case:
  !cx ty bop e1 a t n elems.
    ~is_word_type (expr_type e1) ==>
    (bop = In \/ bop = NotIn) /\
    body_exprs_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once body_expr_ok_def] >>
  rpt gen_tac >> simp[expr_body_pre_def] >> strip_tac >>
  qpat_x_assum `well_typed_expr _ (Builtin _ _ _)` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >>
  gvs[well_typed_binop_def, GSYM membership_element_word_boundary,
      is_prim_word_type_def]
QED
