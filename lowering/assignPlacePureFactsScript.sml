Theory assignPlacePureFacts
Ancestors
  supportedTargets supportedExprTraverse stmtLowering exprLowering

Theorem no_effect_expr_no_mutation:
  (!cenv e. ~supported_expr_exists expr_effect_root e ==>
     ~expr_can_mutate cenv e) /\
  (!cenv es. ~supported_exprs_exists expr_effect_root es ==>
     ~exprs_can_mutate cenv es) /\
  (!cenv oe. ~supported_opt_exists expr_effect_root oe ==>
     ~opt_expr_can_mutate cenv oe) /\
  (!cenv fields. ~supported_fields_exists expr_effect_root fields ==>
     ~named_exprs_can_mutate cenv fields)
Proof
  ho_match_mp_tac expr_can_mutate_ind >>
  simp[expr_can_mutate_def, supported_expr_exists_def, expr_effect_root_def]
QED

Theorem supported_target_pure_not_mutate:
  !tops bt cenv. supported_target_pure tops bt ==>
    ~expr_can_mutate cenv (target_to_expr bt)
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >>
  simp[supported_target_pure_def, target_to_expr_def, expr_can_mutate_def] >>
  metis_tac[supported_pure_no_effect, no_effect_expr_no_mutation]
QED
