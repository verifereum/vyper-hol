(* Conditional support traversal, independent of expression exclusion proofs. *)
Theory abiDecodePtrSupportStmt
Ancestors
  supportedStmts supportedTargets supportedStmtTraverse supportedExprTraverse
  supportedExprs targetPlaceSimCasesBase vyperAST list

Theorem supported_target_info_expr_exclusion[local]:
  !target tops bindings.
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) ==>
  supported_target_info tops bindings target <> NONE ==>
  ~supported_target_exists p target
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> BETA_TAC >>
  rw[supported_target_info_def, supported_expr_exists_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem supported_target_expr_exclusion[local]:
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) /\
  supported_target tops bindings target ==>
  ~supported_target_exists p target
Proof
  Cases_on `target` >>
  simp[supported_target_def, supported_expr_exists_def] >>
  qmatch_goalsub_rename_tac `supported_target_exists p parent` >>
  Cases_on `parent` >> simp[supported_expr_exists_def] >> metis_tac[]
QED

Theorem supported_assignment_expr_exclusion[local]:
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) /\
  supported_assignment tops bindings target e ==>
  ~supported_assignment_exists p target
Proof
  Cases_on `target` >> simp[supported_assignment_def, supported_assignment_exists_def]
  >- (rpt strip_tac
      >- metis_tac[supported_target_expr_exclusion] >>
      Cases_on `supported_target_info tops bindings b` >> gvs[] >>
      rename1 `SOME pt` >> Cases_on `pt` >> gvs[] >>
      `supported_target_info tops bindings b <> NONE` by simp[] >>
      drule_all supported_target_info_expr_exclusion >> simp[]) >>
  rename1 `supported_assignments_exists p targets` >>
  Induct_on `targets` >> simp[supported_assignment_exists_def] >>
  qx_gen_tac `head` >> Cases_on `head` >>
  simp[supported_assignment_exists_def] >> metis_tac[supported_target_expr_exclusion]
QED

Theorem supported_string_reason_expr_exclusion[local]:
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) /\
  supported_string_reason tops e ==> ~supported_expr_exists p e
Proof
  strip_tac >>
  `supported_pure_expr tops e` suffices_by metis_tac[supported_expr_def] >>
  Cases_on `e` >> gvs[supported_string_reason_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >>
  gvs[supported_string_reason_def, supported_pure_expr_def]
QED

Theorem supported_reasons_expr_exclusion[local]:
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) ==>
  (!reason. supported_assert_reason tops reason ==> ~supported_assert_exists p reason) /\
  (!reason. supported_raise_reason tops reason ==> ~supported_raise_exists p reason)
Proof
  strip_tac >> conj_tac >> Cases >>
  simp[supported_assert_reason_def, supported_raise_reason_def,
       supported_assert_exists_def, supported_raise_exists_def] >>
  metis_tac[supported_string_reason_expr_exclusion]
QED

Theorem supported_pure_exprs_expr_exclusion[local]:
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) ==>
  !es. supported_pure_exprs tops es ==> ~supported_exprs_exists p es
Proof
  strip_tac >> Induct >>
  simp[supported_pure_expr_def, supported_expr_exists_def] >>
  metis_tac[supported_expr_def]
QED

Theorem supported_iterator_expr_exclusion[local]:
  (!e. p e ==> ?ann tb target args. e = TypeBuiltin ann tb target args) /\
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) ==>
  !ty iter n. supported_iterator tops ty iter n ==> ~supported_iterator_exists p iter
Proof
  strip_tac >> rpt gen_tac >> Cases_on `iter`
  >- (strip_tac >> drule supported_array_iterator_shape >> strip_tac >>
      simp[supported_iterator_exists_def, supported_expr_exists_def] >>
      strip_tac >> qpat_x_assum `!e. p e ==> _` drule >> simp[]) >>
  simp[supported_iterator_def, supported_iterator_exists_def] >>
  rename1 `~supported_expr_exists p lo /\ ~supported_expr_exists p hi` >>
  Cases_on `lo` >> simp[] >>
  TRY (rename1 `Literal _ lit` >> Cases_on `lit` >> simp[]) >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  imp_res_tac (iffRL supported_expr_def) >>
  qpat_assum `!e. supported_expr tops e ==> _` imp_res_tac >>
  gvs[] >>
  Cases_on `hi` >> gvs[] >>
  TRY (rename1 `Literal _ lit` >> Cases_on `lit` >> gvs[]) >>
  imp_res_tac (iffRL supported_expr_def) >>
  qpat_assum `!e. supported_expr tops e ==> _` imp_res_tac >>
  gvs[supported_expr_exists_def] >>
  qpat_assum `!e. p e ==> _` imp_res_tac >> gvs[]
QED

Theorem supported_aug_target_expr_exclusion[local]:
  (!e. supported_expr tops e ==> ~supported_expr_exists p e) /\
  supported_aug_target tops bindings target ==> ~supported_target_exists p target
Proof
  strip_tac >>
  `supported_target_info tops bindings target <> NONE` suffices_by
    metis_tac[supported_target_info_expr_exclusion] >>
  qpat_x_assum `supported_aug_target _ _ _` mp_tac >>
  Cases_on `supported_target_info tops bindings target` >>
  simp[supported_aug_target_def]
QED

Theorem supported_append_target_expr_exclusion[local]:
  supported_append_target tops target ==> ~supported_target_exists p target
Proof
  Cases_on `target` >>
  simp[supported_append_target_def, supported_expr_exists_def]
QED

Theorem supported_stmts_type_builtin_exclusion:
  (!e. p e ==> ?ann tb target args. e = TypeBuiltin ann tb target args) ==>
  (!tops bindings s.
    (!e. supported_expr tops e ==> ~supported_expr_exists p e) ==>
    supported_stmt tops bindings s ==> ~supported_stmt_expr_exists p s) /\
  (!tops bindings ss.
    (!e. supported_expr tops e ==> ~supported_expr_exists p e) ==>
    supported_stmts tops bindings ss ==> ~supported_stmts_expr_exists p ss)
Proof
  strip_tac >> ho_match_mp_tac supported_stmt_ind >>
  simp[supported_stmt_def, supported_stmt_expr_exists_def, supported_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  imp_res_tac supported_assignment_def >>
  imp_res_tac supported_log_def >>
  imp_res_tac (iffRL supported_expr_def) >>
  imp_res_tac supported_assignment_expr_exclusion >>
  imp_res_tac supported_target_expr_exclusion >>
  imp_res_tac supported_aug_target_expr_exclusion >>
  imp_res_tac supported_append_target_expr_exclusion >>
  imp_res_tac supported_iterator_expr_exclusion >>
  imp_res_tac supported_reasons_expr_exclusion >>
  imp_res_tac supported_pure_exprs_expr_exclusion >>
  gvs[] >> metis_tac[]
QED
