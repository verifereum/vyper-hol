(* Expression closure and compiler interfaces for internal statement bodies. *)
Theory bodyIntCallStmtHelperLabels
Ancestors
  bodyIntCallSupportedExprLabels bodyIntCallMaterialLabels
  stmtLowering moduleLowering supportedStmts supportedStmtTraverse compileEnv supportedExprs list supportedTargets

Theorem declare_local_return_pc:
  declare_local ce id ty st = (ce',out) ==>
  ce'.ce_return_pc = ce.ce_return_pc
Proof
  simp[declare_local_def, comp_bind_def, comp_return_def] >>
  Cases_on `ce.ce_alloca_locals` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem declare_stmt_local_return_pc:
  declare_stmt_local ce s st = (ce',out) ==>
  ce'.ce_return_pc = ce.ce_return_pc
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def] >>
  metis_tac[declare_local_return_pc]
QED

Theorem materialize_internal_params_return_pc:
  !ps ce st ce' out.
    materialize_internal_params ce ps st = (ce',out) ==>
    ce'.ce_return_pc = ce.ce_return_pc
Proof
  Induct >> simp[materialize_internal_params_def, comp_return_def] >>
  rpt gen_tac >> Cases_on `h` >> rename1 `(name,pr)::ps` >>
  Cases_on `pr` >> rename1 `(name,is_stack,param_op)::ps` >>
  simp[materialize_internal_params_def] >>
  Cases_on `is_stack`
  >- (Cases_on `FLOOKUP ce.ce_vars name` >> simp[]
      >- metis_tac[] >>
      rename1 `FLOOKUP ce.ce_vars name = SOME loc` >> Cases_on `loc` >>
      simp[comp_bind_def, comp_ignore_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem supported_expr_structural_closure:
  supported_expr tops e /\ ~expr_has_internal_call e ==>
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e
Proof
  simp[supported_expr_def] >> metis_tac[]
QED

Theorem supported_stmt_rhs_expr:
  (s = Expr e \/ s = Return (SOME e) \/
   (?id ty. s = AnnAssign id ty e) \/ (?target. s = Assign target e) \/
   (?ty target op. s = AugAssign ty target op e) \/
   (?target. s = Append target e)) /\
  supported_stmt tops bindings s /\
  ~supported_stmt_expr_exists expr_internal_call_root s ==>
  supported_expr tops e /\ ~expr_has_internal_call e
Proof
  strip_tac >> gvs[supported_stmt_def, supported_assignment_def,
    supported_stmt_expr_exists_def, supportedExprTraverseTheory.supported_expr_exists_def,
    supportedExprTraverseTheory.expr_has_internal_call_def, supported_expr_def] >>
  metis_tac[]
QED

Theorem supported_stmt_condition_expr:
  (s = If e yes no \/ s = Assert e reason) /\
  supported_stmt tops bindings s ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  strip_tac >> gvs[supported_stmt_def] >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]
QED

Theorem supported_string_reason_expr:
  supported_string_reason tops e ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  Cases_on `e` >> simp[supported_string_reason_def]
  >~ [`Literal ty lit`] >- (Cases_on `lit` >> simp[supported_string_reason_def,
       supported_pure_expr_def,
       supportedExprTraverseTheory.expr_has_internal_call_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_internal_call_root_def]) >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]
QED

Theorem supported_iterator_range_exprs:
  supported_iterator tops ty (Range a b) n ==>
  supported_pure_expr tops a /\ supported_pure_expr tops b /\
  ~expr_has_internal_call a /\ ~expr_has_internal_call b
Proof
  strip_tac >>
  `supported_pure_expr tops a /\ supported_pure_expr tops b` suffices_by
    metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call] >>
  qpat_x_assum `supported_iterator _ _ _ _` mp_tac >>
  simp[supported_iterator_def] >>
  Cases_on `a` >> simp[supported_pure_expr_def] >>
  Cases_on `b` >> simp[supported_pure_expr_def, AllCaseEqs()]
QED

Theorem supported_iterator_array_expr:
  supported_iterator tops ty (Array e) n ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  Cases_on `e` >> simp[supported_iterator_def] >>
  rename1 `Name aty name` >> Cases_on `aty` >> simp[] >>
  rename1 `ArrayT elem bound` >> Cases_on `bound` >>
  simp[supported_pure_expr_def] >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call,
    supported_pure_expr_def]
QED

Theorem supported_assert_reason_expr:
  supported_stmt tops bindings (Assert c (AssertReason e)) ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  simp[supported_stmt_def, supported_assert_reason_def] >>
  metis_tac[supported_string_reason_expr]
QED

Theorem supported_raise_reason_expr:
  supported_stmt tops bindings (Raise (RaiseReason e)) ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  simp[supported_stmt_def, supported_raise_reason_def] >>
  metis_tac[supported_string_reason_expr]
QED

Theorem supported_log_member_expr:
  supported_stmt tops bindings (Log id es) /\ MEM e es ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  simp[supported_stmt_def, supported_log_def, supported_pure_exprs_every, EVERY_MEM] >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]
QED

Theorem supported_target_subscript_expr:
  supported_target tops bindings (SubscriptTarget target_base key) /\
  ~supportedExprTraverse$target_has_internal_call (SubscriptTarget target_base key) ==>
  supported_expr tops key /\ ~expr_has_internal_call key
Proof
  Cases_on `target_base` >>
  simp[supported_target_def, supportedExprTraverseTheory.target_has_internal_call_def,
    supportedExprTraverseTheory.supported_expr_exists_def,
    supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Theorem supported_target_info_subscript_expr:
  supportedTargets$supported_target_info tops bindings (SubscriptTarget target_base key) = SOME pt /\
  ~supportedExprTraverse$target_has_internal_call (SubscriptTarget target_base key) ==>
  supported_expr tops key /\ ~expr_has_internal_call key /\
  ?target_base_pt. supportedTargets$supported_target_info tops bindings target_base = SOME target_base_pt
Proof
  simp[supportedTargetsTheory.supported_target_info_def,
    supportedExprTraverseTheory.target_has_internal_call_def,
    supportedExprTraverseTheory.supported_expr_exists_def,
    supportedExprTraverseTheory.expr_has_internal_call_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem supported_target_info_attribute_target_base:
  supportedTargets$supported_target_info tops bindings (AttributeTarget target_base fname) = SOME pt ==>
  ?target_base_pt. supportedTargets$supported_target_info tops bindings target_base = SOME target_base_pt
Proof
  simp[supportedTargetsTheory.supported_target_info_def, AllCaseEqs()] >> metis_tac[]
QED
