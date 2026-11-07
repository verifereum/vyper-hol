(* Memory case of the body induction (bodyMemory's body_mem_mutual): in and
   not in on an array literal. *)
Theory bodyMemBopInLiteral
Ancestors
  bodyMemoryPreds exprSimBopInLiteralWord compileEnv

Theorem body_literal_operands_mem_ok[local]:
  !cx e1 a t n elems.
    body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_mem_ok cx (e1::elems)
Proof
  simp[body_exprs_mem_ok_def] >>
  metis_tac[body_make_array_children_mem_ok]
QED

Theorem body_literal_mem_typing[local]:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) ==>
  is_word_type (expr_type e1) /\
  builtin_args_length_ok (MakeArray t n) (LENGTH elems)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_body_typing >> strip_tac >>
  conj_tac
  >- (`well_typed_binop ann bop (expr_type e1) a` by
        (gvs[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
             vyperTypeSystemTheory.well_typed_builtin_app_def,
             vyperASTTheory.expr_type_def]) >>
      gvs[] >> metis_tac[membership_checker_lowering_boundary]) >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  qpat_x_assum `well_typed_builtin_app _ (MakeArray _ _) _`
    (mp_then Any mp_tac
       vyperTypeBuiltinsTheory.well_typed_builtin_app_length) >> simp[]
QED

Theorem body_bop_in_literal_mem_case:
  !cx ty bop e1 a t n elems.
    (bop = In \/ bop = NotIn) /\
    body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_mem_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  cheat
QED
