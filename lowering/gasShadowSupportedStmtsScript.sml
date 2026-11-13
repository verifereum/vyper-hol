(* Conditional support closure, independent of expression support proofs. *)
Theory gasShadowSupportedStmts
Ancestors
  gasShadowShape supportedStmts supportedStmtTraverse supportedExprTraverse
  supportedTargets supportedExprs supportedExprForms gasShadow vyperAST list pair combin

Theorem shadow_internal_root[local]:
  expr_internal_call_root (gas_shadow_expr e) = expr_internal_call_root e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, expr_internal_call_root_def] >>
  rename1 `Call ty target args fallback` >> Cases_on `target` >>
  simp[expr_internal_call_root_def]
QED

Theorem shadow_internal_iterator[local]:
  supported_iterator_exists expr_internal_call_root (gas_shadow_iterator iter) =
  supported_iterator_exists expr_internal_call_root iter
Proof
  Cases_on `iter` >> simp[gas_shadow_iterator_def, supported_iterator_exists_def,
    gas_shadow_expr_exists_invariant, shadow_internal_root]
QED

Theorem shadow_internal_assert[local]:
  supported_assert_exists expr_internal_call_root (gas_shadow_assert_reason reason) =
  supported_assert_exists expr_internal_call_root reason
Proof
  Cases_on `reason` >> simp[gas_shadow_assert_reason_def, supported_assert_exists_def,
    gas_shadow_expr_exists_invariant, shadow_internal_root] >>
  rename1 `gas_shadow_custom_error err` >> Cases_on `err` >>
  simp[gas_shadow_custom_error_def, custom_error_exprs_def, EXISTS_APPEND,
    EXISTS_MAP, o_DEF, SF ETA_ss, gas_shadow_expr_exists_invariant, shadow_internal_root]
QED

Theorem shadow_internal_raise[local]:
  supported_raise_exists expr_internal_call_root (gas_shadow_raise_reason reason) =
  supported_raise_exists expr_internal_call_root reason
Proof
  Cases_on `reason` >> simp[gas_shadow_raise_reason_def, supported_raise_exists_def,
    gas_shadow_expr_exists_invariant, shadow_internal_root] >>
  rename1 `gas_shadow_custom_error err` >> Cases_on `err` >>
  simp[gas_shadow_custom_error_def, custom_error_exprs_def, EXISTS_APPEND,
    EXISTS_MAP, o_DEF, SF ETA_ss, gas_shadow_expr_exists_invariant, shadow_internal_root]
QED

Theorem shadow_internal_stmts[local]:
  (!p s. p = expr_internal_call_root ==>
    supported_stmt_expr_exists p (gas_shadow_stmt s) = supported_stmt_expr_exists p s) /\
  (!p ss. p = expr_internal_call_root ==>
    supported_stmts_expr_exists p (MAP gas_shadow_stmt ss) = supported_stmts_expr_exists p ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  simp[gas_shadow_stmt_def, supported_stmt_expr_exists_def,
    gas_shadow_expr_exists_invariant, gas_shadow_shape_assignment_exists,
    shadow_internal_root, shadow_internal_iterator, shadow_internal_assert,
    shadow_internal_raise]
QED

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
  strip_tac >> Cases >> simp[gas_shadow_expr_def, supported_target_def] >>
  rpt gen_tac >> Cases_on `b` >> simp[gas_shadow_expr_def] >> metis_tac[]
QED

Theorem shadow_assignment_support[local]:
  (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)) ==>
  !target tops bindings e. supported_assignment tops bindings target e ==>
    supported_assignment tops bindings (gas_shadow_assignment target) (gas_shadow_expr e)
Proof
  strip_tac >> Cases >> simp[gas_shadow_assignment_def, supported_assignment_def]
  >- (rpt strip_tac >> gvs[AllCaseEqs()]
      >- (disj1_tac >> drule shadow_target_support >> disch_then irule >> simp[]) >>
      Cases_on `supported_target_info tops bindings b` >> gvs[] >>
      Cases_on `x` >> gvs[] >>
      drule shadow_target_info >> disch_then drule >> simp[]) >>
  rpt strip_tac >> gvs[EVERY_MAP] >>
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
  metis_tac[shadow_string_support]
QED

Theorem shadow_loop_iterator_place_root[local]:
  !e attrs.
    OPTION_MAP (\t. FST (place_access t attrs))
      (loop_iterator_place (gas_shadow_expr e)) =
    OPTION_MAP (\t. FST (place_access t attrs)) (loop_iterator_place e)
Proof
  ho_match_mp_tac vyperTypeContractTheory.loop_iterator_place_ind >>
  rpt strip_tac >>
  simp[gas_shadow_expr_def, vyperTypeContractTheory.loop_iterator_place_def,
       vyperTypeSystemTheory.place_access_def, optionTheory.OPTION_MAP_COMPOSE,
       combinTheory.o_DEF]
QED

Theorem shadow_iterator_support[local]:
  (!tops e. supported_pure_expr tops e ==> supported_pure_expr tops (gas_shadow_expr e)) /\
  (!tops e. supported_expr tops e ==> supported_expr tops (gas_shadow_expr e)) ==>
  !iter tops ty n. supported_iterator tops ty iter n ==>
    supported_iterator tops ty (gas_shadow_iterator iter) n
Proof
  strip_tac >> Cases
  >- (rpt gen_tac >> rename1 `Array arr` >> simp[gas_shadow_iterator_def] >>
      `!e. (!t nm. e <> Name t nm) /\ (!t nm. e <> TopLevelName t nm) ==>
           (supported_iterator tops ty (Array e) n <=>
            supported_expr tops e /\
            ~supported_expr_exists (\x. ?t c l r. x = IfExp t c l r) e /\
            (!tgt nid. loop_iterator_place e = SOME tgt ==>
                       FST (place_access tgt []) <> TopLevelNameTarget nid) /\
            (!t fid args drv. e = Call t (IntCall fid) args drv ==>
               ?m nr rr ps ds b.
                 supported_function_decl tops fid Internal =
                   SOME (m,nr,rr,ps,ds,t,b)) /\
            ?bd. expr_type e = ArrayT ty bd /\ bound_length bd <= n)`
        by (Cases >> simp[supported_iterator_def]) >>
      Cases_on `?t nm. arr = Name t nm` >- gvs[gas_shadow_expr_def] >>
      Cases_on `?t nm. arr = TopLevelName t nm` >- gvs[gas_shadow_expr_def] >>
      `(!t nm. gas_shadow_expr arr <> Name t nm) /\
       (!t nm. gas_shadow_expr arr <> TopLevelName t nm)`
        by (Cases_on `arr` >> gvs[gas_shadow_expr_def]) >>
      first_assum (qspec_then `arr` mp_tac) >> impl_tac >- fs[] >>
      disch_then (fn th => REWRITE_TAC [th]) >>
      first_x_assum (qspec_then `gas_shadow_expr arr` mp_tac) >>
      impl_tac >- fs[] >>
      disch_then (fn th => REWRITE_TAC [th]) >>
      strip_tac >>
      conj_tac >- metis_tac[] >>
      conj_tac
      >- (`supported_expr_exists (\x. ?t c l r. x = IfExp t c l r)
             (gas_shadow_expr arr) =
           supported_expr_exists (\x. ?t c l r. x = IfExp t c l r) arr`
            by (irule (CONJUNCT1 gas_shadow_expr_exists_invariant) >>
                Cases >> simp[gas_shadow_expr_def]) >>
          simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          qspecl_then [`arr`, `[]`] mp_tac shadow_loop_iterator_place_root >>
          Cases_on `loop_iterator_place arr` >> gvs[] >> metis_tac[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> Cases_on `arr` >>
          gvs[gas_shadow_expr_def]) >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `!tops e. supported_expr _ _ ==> _` kall_tac >>
  rpt gen_tac >> rename1 `Range a b` >>
  first_assum (qspecl_then [`tops`, `a`] assume_tac) >>
  qpat_assum `!tops e. _` (qspecl_then [`tops`, `b`] assume_tac) >>
  qpat_x_assum `!tops e. _` kall_tac >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[gas_shadow_iterator_def, gas_shadow_expr_def, supported_iterator_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
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
    shadow_internal_stmts] >> rpt strip_tac >> gvs[]
  >- (disj1_tac >> drule shadow_target_support >> disch_then irule >> simp[])
  >- (Cases_on `e` >> gvs[gas_shadow_expr_def, supported_nonnegative_literal_def])
  >- (disj2_tac >> gvs[supported_aug_target_def] >>
      Cases_on `supported_target_info tops bindings target` >> gvs[] >>
      Cases_on `x` >> gvs[] >> drule shadow_target_info >> disch_then drule >> simp[])
  >- (Cases_on `e` >> gvs[gas_shadow_expr_def, supported_nonnegative_literal_def])
  >- (Cases_on `target` >> gvs[supported_append_target_def, gas_shadow_expr_def])
  >- (Cases_on `target` >> gvs[gas_shadow_expr_def]) >>
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
