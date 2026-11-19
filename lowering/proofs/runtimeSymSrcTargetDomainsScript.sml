Theory runtimeSymSrcTargetDomains
Ancestors
  supportedStmts supportedTargets supportedExprTraverse supportedExprs

Theorem runtime_sym_pure_occurrence_domain:
  (!tops a. supported_pure_expr tops a ==>
    !e. supported_expr_exists (\x. x = e) a ==>
      supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e) /\
  (!tops es. supported_pure_exprs tops es ==>
    !e. supported_exprs_exists (\x. x = e) es ==>
      supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e) /\
  (!tops fs. supported_pure_fields tops fs ==>
    !e. supported_fields_exists (\x. x = e) fs ==>
      supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e) /\
  (!tops a. supported_place_expr tops a ==>
    !e. supported_expr_exists (\x. x = e) a ==>
      supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_expr_exists_def] >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> gvs[] >>
  gvs[supported_pure_expr_def, supported_expr_def] >> metis_tac[]
QED

Theorem runtime_sym_effect_occurrence_domain:
  (!tops a. supported_effect_expr tops a ==>
    !e. supported_expr_exists (\x. x = e) a ==>
      supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e) /\
  (!tops a. supported_effect_place_expr tops a ==>
    !e. supported_expr_exists (\x. x = e) a ==>
      supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e)
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  simp[supported_expr_exists_def] >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> gvs[] >>
  gvs[supported_effect_expr_def, supported_expr_def] >>
  metis_tac[runtime_sym_pure_occurrence_domain, supported_expr_def]
QED

Theorem runtime_sym_expr_occurrence_domain:
  supported_expr tops a /\ supported_expr_exists (\x. x = e) a ==>
    supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e
Proof
  simp[supported_expr_def] >> metis_tac[runtime_sym_pure_occurrence_domain,
    runtime_sym_effect_occurrence_domain, supported_expr_def]
QED

Theorem runtime_sym_target_info_domain:
  !bt tops bs pt e.
    supported_target_info tops bs bt = SOME pt /\
    supported_target_exists (\x. x = e) bt ==>
    supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e
Proof
  measureInduct_on `vyperAST$base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[supported_target_info_def, supported_expr_exists_def] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[runtime_sym_expr_occurrence_domain]
QED

Theorem runtime_sym_ordinary_target_domain:
  supported_target tops bs bt /\ supported_target_exists (\x. x = e) bt ==>
    supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e
Proof
  Cases_on `bt` >> simp[supported_target_def, supported_expr_exists_def] >>
  Cases_on `b` >>
  simp[supported_target_def, supported_expr_exists_def] >>
  metis_tac[runtime_sym_expr_occurrence_domain]
QED

Theorem runtime_sym_supported_target_domain:
  (supported_target tops bs bt \/ supported_aug_target tops bs bt) /\
  supported_target_exists (\x. x = e) bt ==>
    supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e
Proof
  simp[supported_aug_target_def] >> rpt strip_tac
  >- metis_tac[runtime_sym_ordinary_target_domain] >>
  Cases_on `supported_target_info tops bs bt` >> gvs[] >>
  Cases_on `x` >> gvs[] >> metis_tac[runtime_sym_target_info_domain]
QED

Theorem runtime_sym_assignment_target_domain:
  supported_assignment tops bs (BaseTarget bt) rhs /\
  supported_target_exists (\x. x = e) bt ==>
    supported_expr tops e \/ supported_place_expr tops e \/ supported_effect_place_expr tops e
Proof
  simp[supported_assignment_def] >> rpt strip_tac
  >- metis_tac[runtime_sym_ordinary_target_domain] >>
  Cases_on `supported_target_info tops bs bt` >> gvs[] >>
  Cases_on `x` >> gvs[] >> metis_tac[runtime_sym_target_info_domain]
QED
