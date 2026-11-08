(* Noncircular semantic-premise audit for the nested candidate. *)
Theory augAssignNestedSemanticAudit
Ancestors
  augAssignNestedApplicabilityProbe exprSimLiteralWord exprSimHyps
  targetPlaceSimCases
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
