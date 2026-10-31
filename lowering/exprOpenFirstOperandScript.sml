(*
 * A builtin's first argument evaluates when the builtin does
 *
 * TOP-LEVEL:
 *   eval_builtin_head_success, eval_type_builtin_head_success — the
 *     first argument's evaluation succeeds
 *   expr_body_pre_builtin_head, expr_body_pre_type_builtin_head —
 *     expr_body_pre holds of it
 *)

Theory exprOpenFirstOperand
Ancestors
  exprSimHyps vyperTypeSystem vyperTypeCallStackSoundness vyperInterpreter
  vyperAST vyperState vyperTypeCallGraph list

Theorem expr_body_pre_builtin_head:
  !cenv cx env ann bi arg args es.
    expr_body_pre cenv cx env (Builtin ann bi (arg::args)) es ==>
    expr_body_pre cenv cx env arg es
Proof
  simp[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem expr_body_pre_type_builtin_head:
  !cenv cx env ann tb ty arg args es.
    expr_body_pre cenv cx env (TypeBuiltin ann tb ty (arg::args)) es ==>
    expr_body_pre cenv cx env arg es
Proof
  simp[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem eval_exprs_head_success:
  !cx arg args es vs es1.
    eval_exprs cx (arg::args) es = (INL vs,es1) ==>
    ?av esA. eval_expr cx arg es = (INL av,esA)
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx arg es` >>
  rename1 `eval_expr cx arg es = (res,st)` >> Cases_on `res` >>
  simp[] >> metis_tac[]
QED

Theorem eval_builtin_head_success:
  !cx ann bi arg args es tv es1.
    eval_expr cx (Builtin ann bi (arg::args)) es = (INL tv,es1) ==>
    ?av esA. eval_expr cx arg es = (INL av,esA)
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
    assert_def, return_def, raise_def] >>
  IF_CASES_TAC >> simp[] >> IF_CASES_TAC
  >- (simp[bind_def] >> Cases_on `eval_expr cx arg es` >>
      rename1 `eval_expr cx arg es = (res,st)` >> Cases_on `res` >>
      simp[] >> metis_tac[]) >>
  simp[bind_def] >> Cases_on `eval_exprs cx (arg::args) es` >>
  rename1 `eval_exprs cx (arg::args) es = (res,st)` >> Cases_on `res` >>
  simp[] >> strip_tac >> drule eval_exprs_head_success >> simp[]
QED

Theorem eval_type_builtin_head_success:
  !cx ann tb ty arg args es tv es1.
    eval_expr cx (TypeBuiltin ann tb ty (arg::args)) es = (INL tv,es1) ==>
    ?av esA. eval_expr cx arg es = (INL av,esA)
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
    assert_def, return_def, raise_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `eval_exprs cx (arg::args) es` >>
  rename1 `eval_exprs cx (arg::args) es = (res,st)` >> Cases_on `res` >>
  simp[] >> strip_tac >> drule eval_exprs_head_success >> simp[]
QED
