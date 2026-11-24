(* Support is preserved in the original declaration environment. *)
Theory gasShadowSupportedExpr
Ancestors
  gasShadow gasShadowCompilePure supportedExprs supportedExprForms vyperAST vyperContext list pair combin

Theorem shadow_builtin_form[local]:
  supported_builtin_form tops ty (gas_shadow_builtin bi) (MAP gas_shadow_expr es) =
    supported_builtin_form tops ty bi es
Proof
  Cases_on `bi` >>
  simp[gas_shadow_builtin_def, supported_builtin_form_def,
       supported_binop_def, builtin_args_length_ok_def] >>
  TRY (Cases_on `e = MsgGas` >> simp[builtin_args_length_ok_def]) >>
  rpt (qmatch_goalsub_rename_tac `MAP gas_shadow_expr xs` >>
       Cases_on `xs` >> simp[builtin_args_length_ok_def, supported_binop_def])
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
  rename1 `StructT id` >> Cases_on `FST id = NONE` >> simp[] >>
  Cases_on `supported_struct_fields tops id` >>
  simp[EVERY_MAP] >> AP_TERM_TAC >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD]
QED

Theorem qualified_place_root_shadow[local]:
  !e. qualified_place_root (gas_shadow_expr e) = qualified_place_root e
Proof
  measureInduct_on `expr_size e` >>
  Cases_on `e` >> simp[qualified_place_root_def, gas_shadow_expr_def, expr_size_def]
QED

Theorem shadow_subscript_place[local]:
  supported_subscript_place tops (gas_shadow_expr e) = supported_subscript_place tops e
Proof
  simp[supported_subscript_place_def, supported_place_info_def, qualified_place_root_shadow]
QED

Theorem gas_shadow_target_indices:
  !target. target_indices (gas_shadow_target target) =
           MAP gas_shadow_expr (target_indices target)
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> simp[gas_shadow_expr_def, target_indices_def, expr_size_def]
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
       shadow_struct_elements, shadow_subscript_place, gas_shadow_target_indices,
       EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >>
  TRY (Cases_on `target` >> gvs[]) >>
  TRY (Cases_on `default` >> gvs[]) >>
  gvs[MEM_MAP] >> metis_tac[]
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
  simp[gas_shadow_expr_def, supported_effect_expr_def, shadow_subscript_place,
       gas_shadow_target_indices, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[gas_shadow_expr_def, supported_effect_expr_def] >>
  TRY (Cases_on `default` >> gvs[]) >>
  gvs[MEM_MAP] >> metis_tac[shadow_pure_support]
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
