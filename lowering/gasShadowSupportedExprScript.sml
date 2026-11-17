(* Support is preserved in the original declaration environment. *)
Theory gasShadowSupportedExpr
Ancestors
  gasShadow gasShadowCompilePure supportedExprs supportedExprForms vyperAST list pair combin

Theorem shadow_literal_tests[local]:
  supported_integer_literal (gas_shadow_expr e) = supported_integer_literal e /\
  supported_nonnegative_literal (gas_shadow_expr e) = supported_nonnegative_literal e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, supported_integer_literal_def,
    supported_nonnegative_literal_def]
QED

Theorem shadow_literal_elements[local]:
  supported_literal_elements tops ty (MAP gas_shadow_expr es) =
    supported_literal_elements tops ty es
Proof
  simp[supported_literal_elements_def, MAP_MAP_o, o_DEF] >>
  Cases_on `ty` >> simp[MAP_MAP_o, o_DEF, EVERY_MAP, ETA_THM]
QED

Theorem shadow_builtin_form[local]:
  supported_builtin_form tops ty (gas_shadow_builtin bi) (MAP gas_shadow_expr es) =
    supported_builtin_form tops ty bi es
Proof
  Cases_on `bi` >> simp[gas_shadow_builtin_def, supported_builtin_form_def,
    shadow_literal_elements] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  rpt (qmatch_goalsub_rename_tac `MAP gas_shadow_expr xs` >>
    Cases_on `xs` >> simp[supported_builtin_form_def, shadow_literal_elements,
      shadow_literal_tests, EVERY_MAP, o_DEF])
QED

Theorem shadow_type_builtin_form[local]:
  supported_type_builtin_form tops ty bi target (MAP gas_shadow_expr es) =
    supported_type_builtin_form tops ty bi target es
Proof
  Cases_on `bi` >> simp[supported_type_builtin_form_def] >>
  rpt (qmatch_goalsub_rename_tac `MAP gas_shadow_expr xs` >>
    Cases_on `xs` >> simp[])
QED

Theorem shadow_struct_elements[local]:
  supported_struct_elements tops ty (MAP (I ## gas_shadow_expr) fields) =
    supported_struct_elements tops ty fields
Proof
  Cases_on `ty` >> simp[supported_struct_elements_def] >>
  rename1 `StructT id` >> Cases_on `supported_struct_fields tops id` >>
  simp[EVERY_MAP] >> AP_TERM_TAC >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem shadow_subscript_place[local]:
  supported_subscript_place tops (gas_shadow_expr e) = supported_subscript_place tops e
Proof
  simp[supported_subscript_place_def, supported_place_info_def]
QED

Theorem shadow_pure_support[local]:
  (!tops e. supported_pure_expr tops e ==>
     supported_pure_expr tops (gas_shadow_expr e)) /\
  (!tops es. supported_pure_exprs tops es ==>
     supported_pure_exprs tops (MAP gas_shadow_expr es)) /\
  (!tops fs. supported_pure_fields tops fs ==>
     supported_pure_fields tops (MAP (I ## gas_shadow_expr) fs)) /\
  (!tops e. supported_place_expr tops e ==>
     supported_place_expr tops (gas_shadow_expr e))
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[gas_shadow_expr_def, supported_pure_expr_def,
       shadow_builtin_form, shadow_type_builtin_form,
       shadow_struct_elements, shadow_subscript_place]
QED

Theorem gas_shadow_supported_pure_expr:
  supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)
Proof
  metis_tac[shadow_pure_support]
QED

Theorem shadow_effect_support[local]:
  (!tops e. supported_effect_expr tops e ==>
     supported_effect_expr tops (gas_shadow_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
     supported_effect_place_expr tops (gas_shadow_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[gas_shadow_expr_def, supported_effect_expr_def,
       shadow_subscript_place] >>
  rpt strip_tac >>
  gvs[gas_shadow_expr_def, supported_effect_expr_def] >>
  metis_tac[shadow_pure_support]
QED

Theorem gas_shadow_supported_effect_expr:
  supported_effect_expr tops e ==> supported_effect_expr tops (gas_shadow_expr e)
Proof
  metis_tac[shadow_effect_support]
QED

Theorem gas_shadow_supported_expr:
  supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)
Proof
  simp[supported_expr_def] >>
  metis_tac[gas_shadow_supported_pure_expr, gas_shadow_supported_effect_expr]
QED
