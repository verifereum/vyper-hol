(* Noncircular semantic-premise audit for the nested candidate. *)
Theory augAssignNestedSemanticAudit
Ancestors
  augAssignNestedApplicabilityProbe exprSimLiteralWord exprSimHyps
  targetPlaceSimCases augAssignNestedCalleeFacts bodySimCallIntcall
Libs computeLib

Theorem nested_audit_rhs_case:
  expr_sim_case F nested_premise_unit.cu_context nested_observation_function
    nested_premise_cenv nested_initial_cx
    (Literal (BaseT (UintT 256)) (IntL 1))
Proof
  rewrite_tac[exprSimHypsDefsTheory.expr_sim_case_def] >> rpt strip_tac >>
  irule compile_literal_word_sim >> simp[compileEnvTheory.is_word_type_def]
QED

Theorem nested_audit_effectful_calls:
  int_calls_target nested_reach_target = [(NONE,"f")]
Proof
  EVAL_TAC
QED

(* Audit boundary: target_idx_case additionally requires expr_sim_case and
   expr_vv_case for the internal-call index, not merely its concrete replay.
   intcall_body_expr_ok reduces this to body_stmts_ok for nested_reach_body.
   The exported Assign/Return/sequence body cases live in bodySimStmtCases,
   which imports bodyAugAssignOther (the obligation under investigation).
   Importing those cases here would make a circular proof dependency. *)

Theorem nested_audit_index_body_ok:
  body_expr_ok nested_initial_cx
    (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
Proof
  irule intcall_body_expr_ok >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `get_module_code nested_initial_cx NONE = SOME nested_reach_tops` by EVAL_TAC >>
  `~nested_initial_cx.in_deploy` by EVAL_TAC >>
  gvs[vyperStateTheory.lift_option_type_def,
      augAssignNestedReachProbeTheory.nested_reach_tops_def,
      vyperInterpreterTheory.lookup_callable_function_def,
      vyperInterpreterTheory.lookup_function_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  simp[nested_replacement_body_ok, bodySimTheory.body_exprs_ok_def,
       bodySimTheory.body_results_ok_def]
QED

Theorem nested_audit_target_case:
  !tops ctx func cenv.
    body_inv tops ctx cenv nested_initial_cx ==>
    target_case F ctx func cenv nested_initial_cx nested_reach_target
Proof
  rpt strip_tac >> irule target_case_all >>
  `body_expr_ok nested_initial_cx
    (Literal (BaseT (UintT 256)) (IntL 0))` by
    (irule bodySimExprCasesTheory.body_expr_ok_intro >>
     simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  drule_all bodySimExprCasesTheory.body_expr_ok_case >> strip_tac >>
  mp_tac nested_audit_index_body_ok >>
  disch_then (mp_then Any mp_tac bodySimExprCasesTheory.body_expr_ok_case) >>
  simp[] >> strip_tac >>
  simp[augAssignNestedReachProbeTheory.nested_reach_target_def,
       targetPlaceSimTheory.target_idx_case_def] >> metis_tac[]
QED
