Theory whitelistLinkedBodyStmtForms
Ancestors
  whitelistLinkedBodyEnv vyperImportRefsProps whitelistCheckerDecls
  whitelistStorageTargetProps whitelistStringReasonProps
  list alist finite_map pred_set pair vyperAST vyperTypeSystem vyperImportRefs
  vyperTypeContract vyperEventArgCompat supportedDecls supportedTypes
  supportedStmts supportedExprForms supportedExprs supportedTargets supportedExprTraverse

Theorem linked_toplevel_target_root[local]:
  linked_body_data_env tops src env /\ (src = NONE \/ FST k <> NONE) /\
  type_place_target env (TopLevelNameTarget k) = SOME vt ==>
  supported_place_root tops k
Proof
  Cases_on `FST k = NONE` >- (
    PairCases_on `k` >>
    simp[well_typed_expr_def, AllCaseEqs(), linked_body_data_env_def] >>
    strip_tac >> gvs[] >>
    qpat_assum `!k t. _ ==> supported_place_root tops k /\ _` drule_all >>
    simp[]) >>
  simp[supported_place_root_def]
QED

Theorem linked_target_info[local]:
  (!e:expr. T) /\
  !bt vt. (src = NONE \/ imported_base_target_refs_ok bt) /\
    type_place_target env bt = SOME vt /\
    linked_body_data_env tops src env /\
    FDOM env.var_types SUBSET set (MAP FST bindings) /\
    (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
         supported_pure_expr tops e) ==>
    IS_SOME (supported_target_info tops bindings bt)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt (gen_tac ORELSE disch_tac) >>
  first_x_assum (CONJUNCTS_THEN assume_tac)
  >~ [`supported_target_info _ _ (NameTarget _)`]
  >- (fs[well_typed_expr_def, AllCaseEqs(), SUBSET_DEF, FLOOKUP_DEF,
          supported_target_info_def] >>
      rename1 `ALOOKUP bindings nm` >>
      Cases_on `ALOOKUP bindings nm` >> gvs[ALOOKUP_NONE])
  >~ [`supported_target_info _ _ (TopLevelNameTarget _)`]
  >- (fs[imported_expr_refs_ok_def] >>
      `supported_place_root tops p` by metis_tac[linked_toplevel_target_root] >>
      drule supported_place_root_target_info >> simp[])
  >~ [`supported_target_info _ _ (SubscriptTarget _ _)`]
  >- (fs[well_typed_expr_def, AllCaseEqs(), imported_expr_refs_ok_def] >>
      simp[supported_target_info_def, supported_expr_def] >> metis_tac[]) >>
  fs[well_typed_expr_def, AllCaseEqs(), imported_expr_refs_ok_def,
     supported_target_info_def] >> metis_tac[]
QED

Theorem linked_value_target[local]:
  (src = NONE \/ imported_base_target_refs_ok bt) /\
  type_place_target env bt = SOME (Type ty) /\
  linked_body_data_env tops src env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
       supported_pure_expr tops e) ==>
  supported_target tops bindings bt
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> Cases_on `bt`
  >~ [`supported_target _ _ (TopLevelNameTarget k)`]
  >- (Cases_on `FST k = NONE`
      >- (PairCases_on `k` >>
          gvs[well_typed_expr_def, AllCaseEqs(), imported_expr_refs_ok_def,
              linked_body_data_env_def, supported_target_def] >>
          metis_tac[storage_value_scalar_target, FST, optionTheory.IS_SOME_EXISTS]) >>
      simp[supported_target_def, supported_scalar_target_def]) >>
  drule_all (cj 2 linked_target_info) >>
  simp[supported_target_def, supported_target_info_def] >>
  rename1 `ALOOKUP bindings nm` >> Cases_on `ALOOKUP bindings nm` >> simp[]
QED

Theorem linked_tuple_targets[local]:
  !ts tys. (src = NONE \/ imported_targets_refs_ok ts) /\
    EVERY (\tgt. case tgt of BaseTarget _ => T | TupleTarget _ => F) ts /\
    LIST_REL (well_typed_atarget env) ts tys /\
    linked_body_data_env tops src env /\
    FDOM env.var_types SUBSET set (MAP FST bindings) /\
    (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
         supported_pure_expr tops e) ==>
    EVERY (\tgt. case tgt of BaseTarget bt => supported_target tops bindings bt
                             | TupleTarget _ => F) ts
Proof
  Induct >> simp[LIST_REL_CONS1, PULL_EXISTS, imported_target_refs_ok_def] >>
  Cases >> simp[well_typed_atarget_def, well_typed_target_def,
                imported_target_refs_ok_def] >>
  metis_tac[linked_value_target]
QED

Theorem linked_assign_supported[local]:
  (src = NONE \/ imported_stmt_refs_ok (Assign tgt e)) /\
  type_stmt env ret (Assign tgt e) = SOME env' /\
  linked_body_data_env tops src env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
       supported_pure_expr tops e) ==>
  supported_assignment tops bindings tgt e
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[supported_assignment_def] >> conj_tac
  >- (fs[type_stmt_def, AllCaseEqs(), imported_stmt_refs_ok_def,
         supported_expr_def] >> metis_tac[]) >>
  Cases_on `tgt` >> simp[] >>
  qpat_x_assum `src = NONE \/ imported_stmt_refs_ok _`
    (assume_tac o REWRITE_RULE [imported_stmt_refs_ok_def, imported_target_refs_ok_def])
  >- (drule type_stmt_assign_base_target_value >> metis_tac[linked_value_target]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp[type_stmt_def, atarget_accepts_def, well_typed_atarget_def, AllCaseEqs(), SF ETA_ss] >>
  strip_tac >> metis_tac[linked_tuple_targets]
QED

Theorem linked_append_supported[local]:
  (src = NONE \/ imported_stmt_refs_ok (Append bt e)) /\
  (!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
          FLOOKUP env.bare_globals k = SOME ty) /\
  type_stmt env ret (Append bt e) = SOME env' /\
  linked_body_data_env tops src env /\
  (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
       supported_pure_expr tops e) /\
  (!bt vt. type_place_target env bt = SOME vt /\
           (src = NONE \/ imported_base_target_refs_ok bt) ==>
           EVERY (supported_pure_expr tops) (target_indices bt)) ==>
  supported_append_target tops bt /\ supported_pure_expr tops e
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp[type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `src = NONE \/ imported_stmt_refs_ok _`
    (assume_tac o REWRITE_RULE [imported_stmt_refs_ok_def]) >>
  reverse conj_tac >- metis_tac[] >>
  `EVERY (supported_pure_expr tops) (target_indices bt)` by metis_tac[] >>
  Cases_on `bt`
  >~ [`supported_append_target _ (TopLevelNameTarget k)`]
  >- (simp[supported_append_target_def] >> Cases_on `FST k = NONE`
      >- (PairCases_on `k` >> gvs[target_mutable_def, imported_expr_refs_ok_def] >>
          rename1 `FLOOKUP env.bare_globals (NONE,id) = NONE` >>
          `FLOOKUP env.bare_global_assignable (NONE,id) = NONE` by
            (Cases_on `FLOOKUP env.bare_global_assignable (NONE,id)` >> simp[] >>
             rename1 `FLOOKUP env.bare_global_assignable (NONE,id) = SOME ty` >>
             qpat_x_assum `!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==> _`
               (qspecl_then [`(NONE,id)`, `ty`] mp_tac) >> simp[]) >>
          gvs[well_typed_expr_def, linked_body_data_env_def] >>
          qpat_x_assum `!k ty. _ ==> supported_storage_value tops k ty`
            (qspecl_then [`(NONE,id)`, `ArrayT elem_ty (Dynamic n)`] mp_tac) >>
          simp[] >> metis_tac[storage_value_dynamic_array]) >>
      simp[supported_storage_dynamic_array_def]) >>
  fs[supported_append_target_def, target_indices_def]
QED

Theorem linked_augassign_supported[local]:
  (src = NONE \/ imported_stmt_refs_ok (AugAssign ty bt op e)) /\
  type_stmt env ret (AugAssign ty bt op e) = SOME env' /\
  linked_body_data_env tops src env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
       supported_pure_expr tops e) ==>
  supported_stmt tops bindings (AugAssign ty bt op e)
Proof
  rw[type_stmt_def, supported_stmt_def, supported_binop_def,
     well_typed_target_def, imported_stmt_refs_ok_def, supported_expr_def] >>
  metis_tac[linked_value_target]
QED

Theorem imported_error_exprs[local]:
  imported_error_refs_ok err ==> imported_exprs_refs_ok (custom_error_exprs err)
Proof
  Cases_on `err` >> simp[imported_error_refs_ok_def, custom_error_exprs_def] >>
  rename1 `imported_exprs_refs_ok (pos ++ MAP SND kw)` >>
  Induct_on `pos` >> simp[imported_expr_refs_ok_def] >>
  Induct_on `kw` >> simp[imported_expr_refs_ok_def, FORALL_PROD]
QED

Theorem linked_custom_error_supported[local]:
  (src = NONE \/ imported_error_refs_ok err) /\
  ALOOKUP mods src = SOME tops /\ custom_error_resolved mods err ==>
  supported_custom_error tops err
Proof
  Cases_on `err` >> rename1 `CustomError k pos kw` >> PairCases_on `k` >>
  rw[imported_error_refs_ok_def, supported_custom_error_def,
     custom_error_resolved_def] >> gvs[]
QED

Theorem linked_log_supported[local]:
  (src = NONE \/ imported_stmt_refs_ok (Log k es)) /\
  type_stmt env ret (Log k es) = SOME env' /\
  linked_body_data_env tops src env /\
  (!es. well_typed_exprs env es /\ (src = NONE \/ imported_exprs_refs_ok es) ==>
        EVERY (supported_pure_expr tops) es) ==>
  supported_log tops k es
Proof
  rw[type_stmt_def, AllCaseEqs(), supported_log_def, supported_pure_exprs_every,
     imported_stmt_refs_ok_def] >- metis_tac[] >>
  Cases_on `FST k = NONE` >> gvs[] >>
  fs[linked_body_data_env_def] >>
  `supported_event_fields tops k = SOME fields` by metis_tac[] >>
  fs[event_arg_compatible_alias_def]
QED

Theorem linked_stmt_leaf_supported:
  linked_body_env tops src tenv env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  (!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
          FLOOKUP env.bare_globals k = SOME ty) /\
  ALOOKUP mods src = SOME tops /\ custom_errors_stmt_ok mods s /\
  (src = NONE \/ imported_stmt_refs_ok s) /\
  (!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
       supported_pure_expr tops e) /\
  (!es. well_typed_exprs env es /\ (src = NONE \/ imported_exprs_refs_ok es) ==>
        EVERY (supported_pure_expr tops) es) /\
  (!bt vt. type_place_target env bt = SOME vt /\
           (src = NONE \/ imported_base_target_refs_ok bt) ==>
           EVERY (supported_pure_expr tops) (target_indices bt)) /\
  type_stmt env ret s = SOME env' /\
  (!c yes no. s <> If c yes no) /\ (!x ty it n b. s <> For x ty it n b) ==>
  supported_stmt tops bindings s
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `linked_body_env _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [linked_body_env_def]) >>
  Cases_on `s` >> simp[]
  >~ [`supported_stmt _ _ (Assign _ _)`]
  >- (simp[supported_stmt_def] >> drule_all linked_assign_supported >> simp[])
  >~ [`supported_stmt _ _ (AugAssign _ _ _ _)`]
  >- (drule_all linked_augassign_supported >> simp[])
  >~ [`supported_stmt _ _ (Append _ _)`]
  >- (simp[supported_stmt_def] >> drule_all linked_append_supported >> simp[])
  >~ [`supported_stmt _ _ (Log _ _)`]
  >- (simp[supported_stmt_def] >> drule_all linked_log_supported >> simp[])
  >~ [`AnnAssign`]
  >- (gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(),
          linked_body_type_facts_def, imported_stmt_refs_ok_def, supported_expr_def] >>
      metis_tac[])
  >~ [`Assert _ r`]
  >- (Cases_on `r` >>
      gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(),
          supported_assert_reason_def, imported_stmt_refs_ok_def, imported_assert_refs_ok_def,
          custom_errors_stmt_ok_def, well_typed_custom_error_def] >>
      metis_tac[supported_string_reason_from_pure, linked_custom_error_supported, imported_error_exprs])
  >~ [`Raise r`]
  >- (Cases_on `r` >>
      gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(),
          supported_raise_reason_def, imported_stmt_refs_ok_def, imported_raise_refs_ok_def,
          custom_errors_stmt_ok_def, well_typed_custom_error_def] >>
      metis_tac[supported_string_reason_from_pure, linked_custom_error_supported, imported_error_exprs])
  >~ [`Return r`]
  >- (Cases_on `r` >> gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(),
          imported_stmt_refs_ok_def, imported_expr_refs_ok_def, supported_expr_def] >> metis_tac[]) >>
  gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(), imported_stmt_refs_ok_def,
      supported_expr_def] >> metis_tac[]
QED
