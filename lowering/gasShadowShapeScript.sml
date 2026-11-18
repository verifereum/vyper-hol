(* The runtime packages' shape side conditions (loweringShapeProps) hold
   of their GAS shadows: gas_shadow_expr keeps every expr_shape_root, so
   the supported-fragment traversals see the same roots on both sides. *)
Theory gasShadowShape
Ancestors
  loweringShapeProps gasShadow gasShadowModuleDefs
  supportedStmtTraverse supportedExprTraverse supportedProgram unitShapeDefs
  vyperAST list rich_list

Theorem gas_shadow_identity_without_msg_gas[local]:
  (!p e. (!ty es. p (Builtin ty (Env MsgGas) es)) /\
    ~supported_expr_exists p e ==> gas_shadow_expr e = e) /\
  (!p t. (!ty es. p (Builtin ty (Env MsgGas) es)) /\
    ~supported_target_exists p t ==> gas_shadow_target t = t) /\
  (!p es. (!ty args. p (Builtin ty (Env MsgGas) args)) /\
    ~supported_exprs_exists p es ==> MAP gas_shadow_expr es = es) /\
  (!p opt. (!ty es. p (Builtin ty (Env MsgGas) es)) /\
    ~supported_opt_exists p opt ==> OPTION_MAP gas_shadow_expr opt = opt) /\
  (!p fields. (!ty es. p (Builtin ty (Env MsgGas) es)) /\
    ~supported_fields_exists p fields ==> MAP (I ## gas_shadow_expr) fields = fields)
Proof
  ho_match_mp_tac supported_expr_exists_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_expr_exists_def, gas_shadow_expr_def, gas_shadow_builtin_def] >>
  TRY COND_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem supported_default_expression_gas_shadow:
  !tops e. supported_default_expression tops e ==> gas_shadow_expr e = e
Proof
  simp[supported_default_expression_def] >> rpt strip_tac >>
  irule (CONJUNCT1 gas_shadow_identity_without_msg_gas) >>
  qexists_tac `expr_msg_gas_root` >> simp[expr_msg_gas_root_def]
QED

Theorem omitted_defaults_gas_shadow_id:
  !tops dflts k. EVERY (supported_default_expression tops) dflts ==>
    MAP gas_shadow_expr (DROP k dflts) = DROP k dflts
Proof
  rpt strip_tac >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  irule supported_default_expression_gas_shadow >>
  qexists_tac `tops` >>
  gvs[EVERY_MEM] >>
  first_x_assum irule >>
  irule (Q.SPECL [`dflts`,`k`,`EL x (DROP k dflts)`] MEM_DROP_IMP) >>
  irule EL_MEM >> simp[]
QED

Theorem gas_shadow_expr_shape_root:
  expr_shape_root (gas_shadow_expr e) = expr_shape_root e
Proof
  Cases_on `e` >>
  simp[gas_shadow_expr_def, expr_shape_root_def] >>
  rw[gas_shadow_builtin_def] >>
  simp[expr_shape_root_def, builtin_arity_def]
QED

Theorem gas_shadow_expr_exists_invariant:
  (!p e. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_expr_exists p (gas_shadow_expr e) = supported_expr_exists p e) /\
  (!p t. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_target_exists p (gas_shadow_target t) = supported_target_exists p t) /\
  (!p es. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_exprs_exists p (MAP gas_shadow_expr es) = supported_exprs_exists p es) /\
  (!p opt. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_opt_exists p (OPTION_MAP gas_shadow_expr opt) = supported_opt_exists p opt) /\
  (!p fields. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_fields_exists p (MAP (I ## gas_shadow_expr) fields) =
    supported_fields_exists p fields)
Proof
  ho_match_mp_tac supported_expr_exists_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[gas_shadow_expr_def, supported_expr_exists_def] >>
  metis_tac[gas_shadow_expr_def]
QED

Theorem gas_shadow_shape_assignment_exists:
  (!p t. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_assignment_exists p (gas_shadow_assignment t) =
    supported_assignment_exists p t) /\
  (!p ts. (!x. p (gas_shadow_expr x) = p x) ==>
    supported_assignments_exists p (MAP gas_shadow_assignment ts) =
    supported_assignments_exists p ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  simp[gas_shadow_assignment_def, supported_assignment_exists_def,
       gas_shadow_expr_exists_invariant]
QED

Theorem gas_shadow_shape_iterator_exists[local]:
  supported_iterator_exists expr_shape_root (gas_shadow_iterator iter) =
  supported_iterator_exists expr_shape_root iter
Proof
  Cases_on `iter` >>
  simp[gas_shadow_iterator_def, supported_iterator_exists_def,
       gas_shadow_expr_exists_invariant, gas_shadow_expr_shape_root]
QED

Theorem gas_shadow_shape_assert_exists[local]:
  supported_assert_exists expr_shape_root (gas_shadow_assert_reason reason) =
  supported_assert_exists expr_shape_root reason
Proof
  Cases_on `reason` >>
  simp[gas_shadow_assert_reason_def, supported_assert_exists_def,
       gas_shadow_expr_exists_invariant, gas_shadow_expr_shape_root] >>
  rename1 `gas_shadow_custom_error err` >> Cases_on `err` >>
  simp[gas_shadow_custom_error_def, custom_error_exprs_def,
       EXISTS_APPEND, EXISTS_MAP, combinTheory.o_DEF, SF ETA_ss,
       gas_shadow_expr_exists_invariant, gas_shadow_expr_shape_root]
QED

Theorem gas_shadow_shape_raise_exists[local]:
  supported_raise_exists expr_shape_root (gas_shadow_raise_reason reason) =
  supported_raise_exists expr_shape_root reason
Proof
  Cases_on `reason` >>
  simp[gas_shadow_raise_reason_def, supported_raise_exists_def,
       gas_shadow_expr_exists_invariant, gas_shadow_expr_shape_root] >>
  rename1 `gas_shadow_custom_error err` >> Cases_on `err` >>
  simp[gas_shadow_custom_error_def, custom_error_exprs_def,
       EXISTS_APPEND, EXISTS_MAP, combinTheory.o_DEF, SF ETA_ss,
       gas_shadow_expr_exists_invariant, gas_shadow_expr_shape_root]
QED

Theorem gas_shadow_shape_stmts_exists_ind[local]:
  (!p s. (!x. p (gas_shadow_expr x) = p x) /\ p = expr_shape_root ==>
    supported_stmt_expr_exists p (gas_shadow_stmt s) =
    supported_stmt_expr_exists p s) /\
  (!p ss. (!x. p (gas_shadow_expr x) = p x) /\ p = expr_shape_root ==>
    supported_stmts_expr_exists p (MAP gas_shadow_stmt ss) =
    supported_stmts_expr_exists p ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  simp[gas_shadow_stmt_def, supported_stmt_expr_exists_def,
       gas_shadow_expr_exists_invariant, gas_shadow_shape_assignment_exists,
       gas_shadow_expr_shape_root, gas_shadow_shape_iterator_exists,
       gas_shadow_shape_assert_exists, gas_shadow_shape_raise_exists]
QED

Theorem gas_shadow_shape_stmts_exists:
  supported_stmts_expr_exists expr_shape_root (MAP gas_shadow_stmt ss) =
  supported_stmts_expr_exists expr_shape_root ss
Proof
  simp[gas_shadow_shape_stmts_exists_ind, gas_shadow_expr_shape_root]
QED

Theorem gas_shadow_external_fn_shape_ok:
  external_fn_shape_ok p ==>
  external_fn_shape_ok (gas_shadow_external_package p)
Proof
  PairCases_on `p` >>
  simp[external_fn_shape_ok_def, gas_shadow_external_package_def,
       gas_shadow_shape_stmts_exists]
QED

Theorem gas_shadow_internal_fn_shape_ok:
  internal_fn_shape_ok p ==>
  internal_fn_shape_ok (gas_shadow_internal_package p)
Proof
  PairCases_on `p` >>
  simp[internal_fn_shape_ok_def, gas_shadow_internal_package_def,
       gas_shadow_shape_stmts_exists]
QED

Theorem gas_shadow_fallback_shape_ok:
  fallback_shape_ok fb ==>
  fallback_shape_ok (OPTION_MAP gas_shadow_fallback_package fb)
Proof
  Cases_on `fb` >- simp[fallback_shape_ok_def] >>
  rename1 `SOME p` >> PairCases_on `p` >>
  simp[fallback_shape_ok_def, gas_shadow_fallback_package_def,
       gas_shadow_shape_stmts_exists]
QED
