(* Finite callee boundaries independent of bodyAugAssignOther. *)
Theory augAssignNestedCalleeFacts
Ancestors
  augAssignNestedReachProbe bodyAssignPlace bodyExprPreFacts
  bodySimExprCases stmtSimSeqEnv

Theorem nested_replacement_expr_ok:
  !cx. body_expr_ok cx nested_reach_replacement
Proof
  gen_tac >>
  rewrite_tac[nested_reach_replacement_def] >>
  irule body_make_array_case >>
  simp[bodySimTheory.body_exprs_ok_def] >> strip_tac >>
  irule body_make_array_case >>
  simp[bodySimTheory.body_exprs_ok_def]
QED

Theorem nested_replacement_stmt_ok:
  !cx. body_stmt_ok cx
    (Assign (BaseTarget (TopLevelNameTarget (NONE,"a"))) nested_reach_replacement)
Proof
  rw[bodySimTheory.body_stmt_ok_def] >>
  irule body_assign_place_case >>
  simp[bodySimTheory.body_base_target_ok_def, nested_replacement_expr_ok] >>
  fs[nested_reach_replacement_def, exprLoweringTheory.lowered_value_type_def] >>
  metis_tac[]
QED
