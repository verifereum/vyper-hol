Theory bodyPtrBopBody
Ancestors
  bodyPtrBopCases bodyPtrBopTypedBytes bodyPtrPreds bodyPtrDefs
  exprPtrUnwrap exprSimOperators exprSimHyps exprLoweringProps
  compileEnv exprSimSource

Theorem bop_nonresidual_pair_ptr_ok:
  bop <> In /\ bop <> NotIn /\ body_exprs_ptr_ok cx [e1;e2] /\
  ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) ==>
  body_expr_ptr_ok cx (Builtin ann (Bop bop) [e1;e2])
Proof
  strip_tac >> simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e1))` by
    metis_tac[expr_body_pre_type_evaluates] >>
  drule_all bop_nonresidual_machine_types >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es` by
    (irule bop_word_pair_sim_ptr >> simp[] >> metis_tac[]) >> simp[] >>
  irule exprPtrUnwrapTheory.expr_vv_sim_ptr_stack >> simp[compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
