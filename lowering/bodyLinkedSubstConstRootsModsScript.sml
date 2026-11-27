Theory bodyLinkedSubstConstRootsMods
Ancestors
  constSubstMods exprSimHypsDefs supportedExprTraverse supportedStmtTraverse
  vyperAST list pair
Libs
  legacyInduction

Triviality linked_subst_targets_no_const_roots:
  (!E t.
    (!bt. ~supported_target_exists p (subst_consts_btarget_mods E bt)) ==>
    ~supported_assignment_exists p (subst_consts_target_mods E t)) /\
  (!E ts.
    (!bt. ~supported_target_exists p (subst_consts_btarget_mods E bt)) ==>
    ~supported_assignments_exists p (subst_consts_targets_mods E ts))
Proof
  ho_match_mp_tac subst_consts_target_mods_ind >>
  simp[subst_consts_target_mods_def, supported_assignment_exists_def]
QED

Theorem linked_subst_stmts_no_const_roots_mods:
  (!e. ~supported_expr_exists (const_name_root_mods mods) (subst_consts_expr_mods E e)) /\
  (!t. ~supported_target_exists (const_name_root_mods mods) (subst_consts_btarget_mods E t)) /\
  (!es. ~supported_exprs_exists (const_name_root_mods mods) (subst_consts_exprs_mods E es)) /\
  (!d. ~supported_opt_exists (const_name_root_mods mods) (subst_consts_opt_mods E d)) /\
  (!fs. ~supported_fields_exists (const_name_root_mods mods) (subst_consts_fields_mods E fs)) ==>
  !ss. ~supported_stmts_expr_exists (const_name_root_mods mods) (subst_consts_stmts_mods E ss)
Proof
  strip_tac >>
  qabbrev_tac `p = const_name_root_mods mods` >>
  `!t. ~supported_assignment_exists p (subst_consts_target_mods E t)` by
    (gen_tac >> irule (cj 1 linked_subst_targets_no_const_roots) >> simp[]) >>
  `!err. ~EXISTS (supported_expr_exists p)
                  (custom_error_exprs (subst_consts_error_mods E err))` by
    (Cases >> fs[subst_consts_error_mods_def, custom_error_exprs_def,
                 supported_exprs_exists_every, supported_fields_exists_every,
                 EXISTS_APPEND, EVERY_MAP, combinTheory.o_DEF]) >>
  `!it. ~supported_iterator_exists p (subst_consts_iter_mods E it)` by
    (Cases >> simp[subst_consts_iter_mods_def, supported_iterator_exists_def]) >>
  `!r. ~supported_assert_exists p (subst_consts_areason_mods E r)` by
    (Cases >> simp[subst_consts_areason_mods_def, supported_assert_exists_def]) >>
  `!r. ~supported_raise_exists p (subst_consts_rreason_mods E r)` by
    (Cases >> simp[subst_consts_rreason_mods_def, supported_raise_exists_def]) >>
  qsuff_tac
    `(!s. ~supported_stmt_expr_exists p (subst_consts_stmt_mods E s)) /\
     (!ss. ~supported_stmts_expr_exists p (subst_consts_stmts_mods E ss))` >- simp[] >>
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  simp[subst_consts_stmt_mods_def, supported_stmt_expr_exists_def]
QED
