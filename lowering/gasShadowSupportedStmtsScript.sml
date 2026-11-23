(* Conditional support closure, independent of expression support proofs. *)
Theory gasShadowSupportedStmts
Ancestors
  gasShadowShape supportedIteratorProps supportedStmts supportedStmtTraverse supportedExprTraverse
  supportedTargets supportedExprs supportedExprForms gasShadowSupportedExpr
  gasShadow vyperExprEffects vyperAST vyperTypeContract constSubst list pair combin

Theorem shadow_target_info[local]:
  (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)) ==>
  !target tops bindings pt.
    supported_target_info tops bindings target = SOME pt ==>
    supported_target_info tops bindings (gas_shadow_target target) = SOME pt
Proof
  strip_tac >> measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt gen_tac >>
  simp[gas_shadow_expr_def, supported_target_info_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  disch_then drule >> simp[]
QED

Theorem shadow_target_support[local]:
  (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)) ==>
  !target tops bindings. supported_target tops bindings target ==>
    supported_target tops bindings (gas_shadow_target target)
Proof
  strip_tac >> drule shadow_target_info >> strip_tac >>
  Cases >> simp[supported_target_def, gas_shadow_expr_def, optionTheory.IS_SOME_EXISTS] >>
  metis_tac[gas_shadow_expr_def]
QED

Theorem shadow_assignment_support[local]:
  (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)) ==>
  !target tops bindings e. supported_assignment tops bindings target e ==>
    supported_assignment tops bindings (gas_shadow_assignment target) (gas_shadow_expr e)
Proof
  strip_tac >> Cases >>
  simp[gas_shadow_assignment_def, supported_assignment_def] >>
  rpt strip_tac >> gvs[EVERY_MAP] >>
  TRY (match_mp_tac (UNDISCH shadow_target_support) >> first_assum ACCEPT_TAC) >>
  irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
  Cases >> simp[gas_shadow_assignment_def] >> metis_tac[shadow_target_support]
QED

Theorem shadow_string_support[local]:
  (!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) ==>
  !e tops. supported_string_reason tops e ==>
    supported_string_reason tops (gas_shadow_expr e)
Proof
  strip_tac >> Cases >> simp[gas_shadow_expr_def, supported_string_reason_def,
    expr_type_def] >> metis_tac[gas_shadow_expr_def]
QED

Theorem shadow_custom_error_kwargs[local]:
  !params kwargs.
    order_custom_error_kwargs params (MAP (I ## gas_shadow_expr) kwargs) =
    OPTION_MAP (MAP gas_shadow_expr) (order_custom_error_kwargs params kwargs)
Proof
  Induct_on `kwargs`
  >- (Cases >> simp[order_custom_error_kwargs_def]) >>
  rpt gen_tac >> PairCases_on `h` >> Cases_on `params` >>
  simp[order_custom_error_kwargs_def] >>
  rename1 `order_custom_error_kwargs (p::ps)` >> PairCases_on `p` >>
  rw[order_custom_error_kwargs_def] >>
  gvs[optionTheory.OPTION_MAP_COMPOSE, combinTheory.o_DEF]
QED

Theorem shadow_custom_error_args[local]:
  order_custom_error_args params
    (CustomError id (MAP gas_shadow_expr pos) (MAP (I ## gas_shadow_expr) kw)) =
  OPTION_MAP (MAP gas_shadow_expr) (order_custom_error_args params (CustomError id pos kw))
Proof
  rw[order_custom_error_args_def, shadow_custom_error_kwargs, NULL_EQ]
QED

Theorem shadow_custom_error_support[local]:
  (!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) /\
  supported_custom_error tops err /\
  EVERY (supported_pure_expr tops) (custom_error_exprs err) ==>
  supported_custom_error tops (gas_shadow_custom_error err) /\
  EVERY (supported_pure_expr tops) (custom_error_exprs (gas_shadow_custom_error err))
Proof
  Cases_on `err` >> rename1 `supported_custom_error _ (CustomError id pos kw)` >>
  PairCases_on `id` >>
  simp[gas_shadow_custom_error_def, custom_error_exprs_def, MAP_MAP_o, o_DEF,
       EVERY_MAP, EVERY_MEM, SF ETA_ss, supported_custom_error_def, custom_error_resolved_def,
       shadow_custom_error_args] >>
  rpt (CASE_TAC >> gvs[MAP_MAP_o, o_DEF, SF ETA_ss]) >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem shadow_reason_support[local]:
  (!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) ==>
  (!r tops. supported_assert_reason tops r ==>
    supported_assert_reason tops (gas_shadow_assert_reason r)) /\
  (!r tops. supported_raise_reason tops r ==>
    supported_raise_reason tops (gas_shadow_raise_reason r))
Proof
  strip_tac >> conj_tac >> Cases >>
  simp[gas_shadow_assert_reason_def, gas_shadow_raise_reason_def,
    supported_assert_reason_def, supported_raise_reason_def] >>
  metis_tac[shadow_string_support, shadow_custom_error_support]
QED

Theorem shadow_iterator_support[local]:
  (!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) /\
  (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)) ==>
  !iter tops ty n. supported_iterator tops ty iter n ==>
    supported_iterator tops ty (gas_shadow_iterator iter) n
Proof
  strip_tac >> Cases
  >- (rpt gen_tac >> rename1 `Array arr` >> simp[gas_shadow_iterator_def] >>
      Cases_on `?t nm. arr = Name t nm` >- gvs[gas_shadow_expr_def] >>
      Cases_on `?t nm. arr = TopLevelName t nm` >- gvs[gas_shadow_expr_def] >>
      `(!t nm. gas_shadow_expr arr <> Name t nm) /\
       (!t nm. gas_shadow_expr arr <> TopLevelName t nm)`
        by (Cases_on `arr` >> gvs[gas_shadow_expr_def]) >>
      `(!t nm. arr <> Name t nm) /\
       (!t nm. arr <> TopLevelName t nm)` by metis_tac[] >>
      asm_simp_tac bool_ss [supported_non_name_array_iterator] >>
      strip_tac >> conj_tac
      >- (rpt gen_tac >> strip_tac >> Cases_on `arr` >>
          gvs[gas_shadow_expr_def] >> res_tac) >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `!tops e. supported_expr _ _ ==> _` kall_tac >>
  rpt gen_tac >> rename1 `Range a b` >>
  first_assum (qspecl_then [`tops`, `a`] assume_tac) >>
  qpat_assum `!tops e. _` (qspecl_then [`tops`, `b`] assume_tac) >>
  qpat_x_assum `!tops e. _` kall_tac >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[gas_shadow_iterator_def, gas_shadow_expr_def, supported_iterator_def,
      subst_consts_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem shadow_append_support[local]:
  (!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) ==>
  !t tops. supported_append_target tops t ==>
    supported_append_target tops (gas_shadow_target t)
Proof
  strip_tac >> Cases >>
  simp[supported_append_target_def, gas_shadow_expr_def, gas_shadow_target_indices,
       target_indices_def, EVERY_APPEND, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  metis_tac[]
QED

Theorem shadow_stmt_support[local]:
  ((!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) /\
   (!tops e. supported_effect_expr tops e ==> supported_effect_expr tops (gas_shadow_expr e)) /\
   (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e))) ==>
  (!tops bindings s. supported_stmt tops bindings s ==>
    supported_stmt tops bindings (gas_shadow_stmt s)) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    supported_stmts tops bindings (MAP gas_shadow_stmt ss))
Proof
  strip_tac >> ho_match_mp_tac supported_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[gas_shadow_stmt_def, supported_stmt_def, shadow_assignment_support,
       shadow_target_support, shadow_iterator_support, shadow_reason_support,
       shadow_append_support, supported_binop_def] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[shadow_target_support]
  >- (disj2_tac >> gvs[supported_aug_target_def] >>
      Cases_on `supported_target_info tops bindings target` >> gvs[] >>
      drule shadow_target_info >> disch_then drule >> simp[]) >>
  gvs[supported_log_def, supported_pure_exprs_every, EVERY_MAP, MAP_MAP_o, o_DEF] >>
  conj_tac
  >- (irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `supported_event_fields tops id` >>
  gvs[listTheory.LIST_REL_MAP1, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem gas_shadow_supported_stmts_from_expr:
  ((!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) /\
   (!tops e. supported_effect_expr tops e ==> supported_effect_expr tops (gas_shadow_expr e)) /\
   (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e))) ==>
  !tops bindings ss. supported_stmts tops bindings ss ==>
    supported_stmts tops bindings (MAP gas_shadow_stmt ss)
Proof
  metis_tac[shadow_stmt_support]
QED
