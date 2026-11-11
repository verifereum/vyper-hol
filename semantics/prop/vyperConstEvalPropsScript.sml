(* The frontend's compile-time constant values (vyperConstEval) agree with
   the interpreter. *)
Theory vyperConstEvalProps
Ancestors
  vyperConstEval vyperEvalPureExpr vyperContext vyperState vyperValue vyperAST
  vyperValueOperation

Theorem evaluate_builtin_closed[local]:
  closed_builtin b /\ EVERY (\t. ?bt. t = BaseT bt) tys ==>
  evaluate_builtin cx acc (BaseT bt) b tys vs =
  evaluate_builtin empty_evaluation_context empty_accounts (BaseT bt) b tys vs
Proof
  Cases_on `b` >> rw[closed_builtin_def] >>
  simp[evaluate_builtin_def, evaluate_type_def] >>
  Cases_on `tys` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[evaluate_type_def]
QED

Theorem eval_constant_pure:
  (!e v. eval_constant e = SOME v ==>
     (?bt. expr_type e = BaseT bt) /\
     !cx st. eval_pure_expr cx st e = SOME (Value v)) /\
  (!es vs. eval_constants es = SOME vs ==>
     EVERY (\t. ?bt. t = BaseT bt) (MAP expr_type es) /\
     !cx st. eval_pure_exprs cx st es = SOME vs)
Proof
  ho_match_mp_tac eval_constant_ind >>
  rw[eval_constant_def, AllCaseEqs()] >>
  gvs[expr_type_def, eval_pure_expr_def, evaluate_literal_def,
      read_result_def, return_def, evaluate_type_builtin_def,
      type_builtin_args_length_ok_def] >>
  `b <> Len /\ b <> Bop In /\ b <> Bop NotIn /\ ~precompile_builtin b` by
    (Cases_on `b` >> gvs[closed_builtin_def]) >>
  gvs[] >>
  drule_all evaluate_builtin_closed >> simp[]
QED

(* A computed value is what the interpreter returns in any context and state,
   leaving the state unchanged. *)
Theorem eval_constant_sound:
  eval_constant e = SOME v ==>
  eval_expr cx e st = (INL (Value v), st)
Proof
  strip_tac >> irule eval_pure_expr_to_eval_expr_some >>
  drule (cj 1 eval_constant_pure) >> simp[]
QED
