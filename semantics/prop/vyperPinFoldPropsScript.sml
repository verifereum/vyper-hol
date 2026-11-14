Theory vyperPinFoldProps
Ancestors
  vyperPinFold vyperConstEval vyperEvalPureExpr vyperContext vyperState vyperValue vyperAST
  vyperValueOperation

Theorem pin_constant_literal_evaluate:
  pin_constant_literal v = SOME l ==> evaluate_literal l = v
Proof
  Cases_on `v` >> rw[pin_constant_literal_def, constant_literal_def] >>
  simp[evaluate_literal_def]
QED

Theorem evaluate_builtin_pin_closed[local]:
  pin_foldable_builtin b /\ EVERY (\t. ?bt. t = BaseT bt) tys ==>
  evaluate_builtin cx acc (BaseT bt) b tys vs =
  evaluate_builtin empty_evaluation_context empty_accounts (BaseT bt) b tys vs
Proof
  Cases_on `b` >> rw[pin_foldable_builtin_def] >>
  simp[evaluate_builtin_def, evaluate_type_def] >>
  Cases_on `tys` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[evaluate_type_def]
QED

Theorem pin_literal_values_pure:
  pin_literal_values es = SOME vs ==>
  eval_pure_exprs cx st es = SOME vs
Proof
  qid_spec_tac `vs` >> Induct_on `es` >>
  simp[pin_literal_values_def, eval_pure_expr_def] >>
  Cases_on `h` >> simp[pin_literal_values_def] >>
  rw[AllCaseEqs()] >>
  gvs[eval_pure_expr_def, read_result_def, return_def]
QED
