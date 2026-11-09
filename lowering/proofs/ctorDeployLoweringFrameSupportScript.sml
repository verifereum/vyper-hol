Theory ctorDeployLoweringFrameSupport
Ancestors
  supportedStmts supportedExprTraverse supportedExprs supportedExprForms
  supportedTargets supportedStmtTraverse exprLowering allocLimits vyperAST

Theorem deploy_frame_supported_builtin_not_extcode:
  supported_builtin_form tops ty bi es ==> ~is_extcode (Builtin ty bi es)
Proof
  Cases_on `bi` >> simp[is_extcode_def] >>
  rename1 `Acc a` >> Cases_on `a` >>
  simp[is_extcode_def, supported_builtin_form_def] >>
  Cases_on `es` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem deploy_frame_supported_pure_no_extcode:
  (!tops e. supported_pure_expr tops e ==>
    ~supported_expr_exists is_extcode e) /\
  (!tops es. supported_pure_exprs tops es ==>
    ~supported_exprs_exists is_extcode es) /\
  (!tops fields. supported_pure_fields tops fields ==>
    ~supported_fields_exists is_extcode fields) /\
  (!tops e. supported_place_expr tops e ==>
    ~supported_expr_exists is_extcode e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, supported_expr_exists_def, is_extcode_def] >>
  metis_tac[deploy_frame_supported_builtin_not_extcode]
QED

Theorem deploy_frame_supported_effect_no_extcode:
  (!tops e. supported_effect_expr tops e ==>
    ~supported_expr_exists is_extcode e) /\
  (!tops e. supported_effect_place_expr tops e ==>
    ~supported_expr_exists is_extcode e)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  simp[supported_effect_expr_def, supported_expr_exists_def, is_extcode_def] >>
  metis_tac[deploy_frame_supported_pure_no_extcode]
QED

Theorem deploy_frame_supported_expr_no_extcode:
  supported_expr tops e ==> ~supported_expr_exists is_extcode e
Proof
  simp[supported_expr_def] >>
  metis_tac[deploy_frame_supported_pure_no_extcode,
            deploy_frame_supported_effect_no_extcode]
QED

Theorem deploy_frame_supported_target_info_no_extcode:
  !target tops bindings pt.
    supported_target_info tops bindings target = SOME pt ==>
    ~supported_target_exists is_extcode target
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >>
  gvs[supported_target_info_def, supported_expr_exists_def, AllCaseEqs(),
      expr_size_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  metis_tac[deploy_frame_supported_expr_no_extcode]
QED

Theorem deploy_frame_supported_target_no_extcode:
  supported_target tops bindings target ==>
  ~supported_target_exists is_extcode target
Proof
  Cases_on `target` >>
  simp[supported_target_def, supported_expr_exists_def] >>
  Cases_on `b` >>
  simp[supported_target_def, supported_expr_exists_def] >>
  metis_tac[deploy_frame_supported_expr_no_extcode]
QED

Theorem deploy_frame_supported_assignment_no_extcode:
  supported_assignment tops bindings target e ==>
  ~supported_assignment_exists is_extcode target /\
  ~supported_expr_exists is_extcode e
Proof
  Cases_on `target`
  >- (simp[supported_assignment_def, supported_assignment_exists_def] >>
      Cases_on `supported_target_info tops bindings b` >> simp[]
      >- metis_tac[deploy_frame_supported_expr_no_extcode,
                   deploy_frame_supported_target_no_extcode] >>
      Cases_on `x` >> simp[] >>
      metis_tac[deploy_frame_supported_expr_no_extcode,
                deploy_frame_supported_target_no_extcode,
                deploy_frame_supported_target_info_no_extcode]) >>
  simp[supported_assignment_def, supported_assignment_exists_def] >>
  strip_tac >>
  reverse conj_tac >- metis_tac[deploy_frame_supported_expr_no_extcode] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  rename1 `supported_assignments_exists is_extcode targets` >>
  Induct_on `targets` >> simp[supported_assignment_exists_def] >>
  Cases_on `h` >> simp[supported_assignment_exists_def] >>
  metis_tac[deploy_frame_supported_target_no_extcode]
QED

Theorem deploy_frame_supported_string_no_extcode:
  supported_string_reason tops e ==> ~supported_expr_exists is_extcode e
Proof
  Cases_on `e` >> simp[supported_string_reason_def] >>
  all_tac >~ [`Literal ty lit`]
  >- (Cases_on `lit` >>
      simp[supported_string_reason_def, supported_expr_exists_def, is_extcode_def]) >>
  metis_tac[deploy_frame_supported_pure_no_extcode]
QED

Theorem deploy_frame_supported_iterator_no_extcode:
  supported_iterator tops ty iter n ==>
  ~supported_iterator_exists is_extcode iter
Proof
  Cases_on `iter`
  >- (strip_tac >> drule supported_array_iterator_shape >> strip_tac >>
      simp[supported_iterator_exists_def, supported_expr_exists_def, is_extcode_def]) >>
  rename1 `Range a b` >>
  `supported_iterator tops ty (Range a b) n ==>
   (supported_pure_expr tops a /\ supported_pure_expr tops b) \/
   (?at al bt bl. a = Literal at al /\ b = Literal bt bl)` by
    (Cases_on `a` >> Cases_on `b` >>
     simp[supported_iterator_def] >> metis_tac[]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  simp[supported_iterator_exists_def, supported_expr_exists_def, is_extcode_def] >>
  metis_tac[deploy_frame_supported_pure_no_extcode]
QED

Theorem deploy_frame_supported_stmts_no_extcode_mutual:
  (!tops bindings s. supported_stmt tops bindings s ==>
    ~supported_stmt_expr_exists is_extcode s) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    ~supported_stmts_expr_exists is_extcode ss)
Proof
  ho_match_mp_tac supported_stmt_ind >>
  simp[supported_stmt_def, supported_stmt_expr_exists_def] >>
  rpt conj_tac >> rpt gen_tac >>
  all_tac >~ [`supported_aug_target tops bindings target`]
  >- (Cases_on `supported_target_info tops bindings target` >>
      simp[supported_aug_target_def]
      >- metis_tac[deploy_frame_supported_expr_no_extcode,
                   deploy_frame_supported_target_no_extcode] >>
      Cases_on `x` >> simp[] >>
      metis_tac[deploy_frame_supported_expr_no_extcode,
                deploy_frame_supported_target_no_extcode,
                deploy_frame_supported_target_info_no_extcode]) >>
  all_tac >~ [`supported_append_target tops target`]
  >- (Cases_on `target` >>
      simp[supported_append_target_def, supported_expr_exists_def] >>
      metis_tac[deploy_frame_supported_pure_no_extcode]) >>
  all_tac >~ [`supported_assert_reason tops reason`]
  >- (Cases_on `reason` >>
      simp[supported_assert_reason_def, supported_assert_exists_def] >>
      metis_tac[deploy_frame_supported_string_no_extcode,
                deploy_frame_supported_pure_no_extcode]) >>
  all_tac >~ [`supported_raise_reason tops reason`]
  >- (Cases_on `reason` >>
      simp[supported_raise_reason_def, supported_raise_exists_def] >>
      metis_tac[deploy_frame_supported_string_no_extcode]) >>
  simp[supported_expr_exists_def, supported_log_def] >>
  metis_tac[deploy_frame_supported_expr_no_extcode,
            deploy_frame_supported_pure_no_extcode,
            deploy_frame_supported_assignment_no_extcode,
            deploy_frame_supported_iterator_no_extcode]
QED

Theorem deploy_frame_supported_stmts_no_extcode:
  supported_stmts tops bindings ss ==>
  ~supported_stmts_expr_exists is_extcode ss
Proof
  metis_tac[cj 2 deploy_frame_supported_stmts_no_extcode_mutual]
QED

Theorem deploy_frame_expr_exists_disj:
  (!p e q. supported_expr_exists (\x. p x \/ q x) e <=>
    supported_expr_exists p e \/ supported_expr_exists q e) /\
  (!p t q. supported_target_exists (\x. p x \/ q x) t <=>
    supported_target_exists p t \/ supported_target_exists q t) /\
  (!p es q. supported_exprs_exists (\x. p x \/ q x) es <=>
    supported_exprs_exists p es \/ supported_exprs_exists q es) /\
  (!p oe q. supported_opt_exists (\x. p x \/ q x) oe <=>
    supported_opt_exists p oe \/ supported_opt_exists q oe) /\
  (!p fs q. supported_fields_exists (\x. p x \/ q x) fs <=>
    supported_fields_exists p fs \/ supported_fields_exists q fs)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  simp[supported_expr_exists_def] >> metis_tac[]
QED

Theorem deploy_frame_assignment_exists_disj:
  (!p t q. supported_assignment_exists (\x. p x \/ q x) t <=>
    supported_assignment_exists p t \/ supported_assignment_exists q t) /\
  (!p ts q. supported_assignments_exists (\x. p x \/ q x) ts <=>
    supported_assignments_exists p ts \/ supported_assignments_exists q ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  simp[supported_assignment_exists_def, deploy_frame_expr_exists_disj] >> metis_tac[]
QED

Theorem deploy_frame_stmt_exists_disj:
  (!p s q. supported_stmt_expr_exists (\x. p x \/ q x) s <=>
    supported_stmt_expr_exists p s \/ supported_stmt_expr_exists q s) /\
  (!p ss q. supported_stmts_expr_exists (\x. p x \/ q x) ss <=>
    supported_stmts_expr_exists p ss \/ supported_stmts_expr_exists q ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  simp[supported_stmt_expr_exists_def, deploy_frame_expr_exists_disj,
       deploy_frame_assignment_exists_disj] >>
  rpt conj_tac >> rpt gen_tac >>
  all_tac >~ [`supported_assert_exists _ reason`]
  >- (Cases_on `reason` >>
      simp[supported_assert_exists_def, GSYM supported_exprs_exists_every,
           deploy_frame_expr_exists_disj] >> metis_tac[]) >>
  all_tac >~ [`supported_raise_exists _ reason`]
  >- (Cases_on `reason` >>
      simp[supported_raise_exists_def, GSYM supported_exprs_exists_every,
           deploy_frame_expr_exists_disj]) >>
  all_tac >~ [`supported_iterator_exists _ iter`]
  >- (Cases_on `iter` >>
      simp[supported_iterator_exists_def, deploy_frame_expr_exists_disj] >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem deploy_frame_remove_extcode_guard:
  ~supported_stmts_expr_exists is_extcode ss /\
  ~supported_stmts_expr_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) ss ==>
  ~supported_stmts_expr_exists (\e. ~alloc_limits_expr cenv e) ss
Proof
  `(!e. is_extcode e \/ (~is_extcode e /\ ~alloc_limits_expr cenv e) <=>
         is_extcode e \/ ~alloc_limits_expr cenv e)` by metis_tac[] >>
  `supported_stmts_expr_exists
     (\e. is_extcode e \/ (~is_extcode e /\ ~alloc_limits_expr cenv e)) ss =
   supported_stmts_expr_exists
     (\e. is_extcode e \/ ~alloc_limits_expr cenv e) ss` by
    (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]) >>
  gvs[deploy_frame_stmt_exists_disj] >> metis_tac[]
QED
