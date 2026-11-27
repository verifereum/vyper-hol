(* Support at the substituted body of the selected checked declaration. *)
Theory bodyCheckedLinkedSupportMods
Ancestors
  whitelistLinkedBodyStmts whitelistLinkedBodyExprs whitelistLinkedBodyStmtForms
  whitelistLinkedBodyRange vyperImportRefsProps vyperTypeContractStaticMaps
  constSubstModsCorrect bodyQualifiedStmtSupport constSubst constSubstMods
  vyperAST vyperTypeContract alist finite_map vyperTypeSystem vyperImportRefs
  whitelistLinkedBodyEnv supportedProgram supportedStmts supportedExprs
  supportedStmtTraverse
Libs
  legacyInduction

Triviality linked_subst_operands_fixed:
  (!id rhs. ALOOKUP E id = SOME rhs ==> subst_consts_expr_mods E rhs = rhs) ==>
  (!e. subst_consts_expr_mods E (subst_consts_expr_mods E e) =
       subst_consts_expr_mods E e) /\
  (!t. subst_consts_btarget_mods E (subst_consts_btarget_mods E t) =
       subst_consts_btarget_mods E t) /\
  (!es. subst_consts_exprs_mods E (subst_consts_exprs_mods E es) =
        subst_consts_exprs_mods E es) /\
  (!d. subst_consts_opt_mods E (subst_consts_opt_mods E d) =
       subst_consts_opt_mods E d) /\
  (!fs. subst_consts_fields_mods E (subst_consts_fields_mods E fs) =
        subst_consts_fields_mods E fs)
Proof
  strip_tac >> ho_match_mp_tac fold_const_expr_ind >>
  simp[subst_consts_expr_mods_def] >>
  rpt gen_tac >> PairCases_on `ns` >>
  Cases_on `ALOOKUP E (ns0,ns1)` >> simp[subst_consts_expr_mods_def] >>
  first_x_assum drule >> simp[]
QED

Triviality linked_subst_targets_fixed:
  (!E t.
    (!bt. subst_consts_btarget_mods E (subst_consts_btarget_mods E bt) =
          subst_consts_btarget_mods E bt) ==>
    subst_consts_target_mods E (subst_consts_target_mods E t) =
    subst_consts_target_mods E t) /\
  (!E ts.
    (!bt. subst_consts_btarget_mods E (subst_consts_btarget_mods E bt) =
          subst_consts_btarget_mods E bt) ==>
    subst_consts_targets_mods E (subst_consts_targets_mods E ts) =
    subst_consts_targets_mods E ts)
Proof
  ho_match_mp_tac subst_consts_target_mods_ind >>
  simp[subst_consts_target_mods_def]
QED

Triviality checked_linked_body_subst_fixed:
  check_contract dep layouts addr mods = SOME art ==>
  !ss. subst_consts_stmts_mods (consts_env_mods mods)
         (subst_consts_stmts_mods (consts_env_mods mods) ss) =
       subst_consts_stmts_mods (consts_env_mods mods) ss
Proof
  strip_tac >> drule checked_consts_env_mods_closed >> strip_tac >>
  qabbrev_tac `E = consts_env_mods mods` >>
  `!id rhs. ALOOKUP E id = SOME rhs ==> subst_consts_expr_mods E rhs = rhs` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_then strip_assume_tac linked_subst_operands_fixed >>
  `!t. subst_consts_target_mods E (subst_consts_target_mods E t) =
       subst_consts_target_mods E t` by
    (gen_tac >> irule (cj 1 linked_subst_targets_fixed) >> simp[]) >>
  `!err. subst_consts_error_mods E (subst_consts_error_mods E err) =
         subst_consts_error_mods E err` by
    (Cases >> simp[subst_consts_error_mods_def]) >>
  `!it. subst_consts_iter_mods E (subst_consts_iter_mods E it) =
        subst_consts_iter_mods E it` by
    (Cases >> simp[subst_consts_iter_mods_def]) >>
  `!r. subst_consts_rreason_mods E (subst_consts_rreason_mods E r) =
       subst_consts_rreason_mods E r` by
    (Cases >> simp[subst_consts_rreason_mods_def]) >>
  `!r. subst_consts_areason_mods E (subst_consts_areason_mods E r) =
       subst_consts_areason_mods E r` by
    (Cases >> simp[subst_consts_areason_mods_def]) >>
  qsuff_tac
    `(!s. subst_consts_stmt_mods E (subst_consts_stmt_mods E s) =
          subst_consts_stmt_mods E s) /\
     (!ss. subst_consts_stmts_mods E (subst_consts_stmts_mods E ss) =
           subst_consts_stmts_mods E ss)` >- simp[] >>
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >> simp[subst_consts_stmt_mods_def]
QED

Triviality qualified_body_custom_errors:
  (!s. qualified_stmt_decls_ok mods s ==> custom_errors_stmt_ok mods s) /\
  (!ss. qualified_stmts_decls_ok mods ss ==> custom_errors_stmts_ok mods ss)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  simp[qualified_stmt_decls_ok_def, custom_errors_stmt_ok_def] >>
  rpt conj_tac >> rpt gen_tac
  >- (rename1 `qualified_stmt_decls_ok _ (Assert _ reason) ==> _` >>
      Cases_on `reason` >> simp[qualified_stmt_decls_ok_def, custom_errors_stmt_ok_def] >>
      rename1 `qualified_custom_error_ok _ err ==> _` >>
      Cases_on `err` >> simp[]) >>
  rename1 `qualified_stmt_decls_ok _ (Raise reason) ==> _` >>
  Cases_on `reason` >> simp[qualified_stmt_decls_ok_def, custom_errors_stmt_ok_def] >>
  rename1 `qualified_custom_error_ok _ err ==> _` >>
  Cases_on `err` >> simp[]
QED

Triviality linked_main_structs_nonempty:
  check_contract mode layouts addr mods = SOME art /\ ALOOKUP mods src = SOME tops ==>
  !name. ~MEM (StructDecl name []) tops
Proof
  rpt strip_tac >>
  drule_all check_contract_toplevel_decl_MEM_checked >>
  simp[check_toplevel_decl_def]
QED

Triviality linked_checked_leaf:
  ALOOKUP mods src = SOME tops /\
  (src = NONE ==> !name. ~MEM (StructDecl name []) tops) /\
  linked_body_env tops src tenv env /\
  (src = NONE \/ imported_stmt_refs_ok s) /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  custom_errors_stmt_ok mods s /\ type_stmt env ret s = SOME out /\
  (!c yes no. s <> If c yes no) /\ (!x ty it n b. s <> For x ty it n b) ==>
  supported_stmt tops bindings s
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
           FLOOKUP env.bare_globals k = SOME ty` by
    fs[linked_body_env_def] >>
  drule linked_well_typed_expr_supported >>
  disch_then (qspec_then `tenv` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `!e. well_typed_expr env e /\ (src = NONE \/ imported_expr_refs_ok e) ==>
       supported_pure_expr tops e` by
    (gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     qpat_assum `!env e. well_typed_expr env e ==> _`
       (qspecl_then [`env`, `e`] mp_tac) >> simp[]) >>
  `!es. well_typed_exprs env es /\ (src = NONE \/ imported_exprs_refs_ok es) ==>
        EVERY (supported_pure_expr tops) es` by
    (gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     qpat_assum `!env es. well_typed_exprs env es ==> _`
       (qspecl_then [`env`, `es`] mp_tac) >> simp[]) >>
  `!bt vt. type_place_target env bt = SOME vt /\
           (src = NONE \/ imported_base_target_refs_ok bt) ==>
           EVERY (supported_pure_expr tops) (target_indices bt)` by
    (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     qpat_assum `!env tgt. IS_SOME (type_place_target env tgt) ==> _`
       (qspecl_then [`env`, `bt`] mp_tac) >> simp[]) >>
  drule_all linked_stmt_leaf_supported >> simp[]
QED

Theorem checked_linked_substituted_body_supported_mode:
  check_contract mode layouts addr mods = SOME art /\
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  linked_body_env tops src tenv env /\
  FDOM env.var_types = set (MAP FST args) /\ ALL_DISTINCT (MAP FST args) /\
  b = subst_consts_stmts_mods (consts_env_mods mods) ss /\
  IS_SOME (type_stmts env ret b) /\ qualified_stmts_decls_ok mods b ==>
  supported_stmts tops (args ++ supported_stmts_bindings T b ++ supported_stmts_bindings F b) b
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Q.SUBGOAL_THEN `src = NONE \/ imported_stmts_refs_ok b` assume_tac
  >- (Cases_on `src` >> simp[] >>
      rename1 `ALOOKUP mods (SOME m) = SOME tops` >>
      `MEM (SOME m,tops) mods` by metis_tac[ALOOKUP_MEM] >>
      drule_all check_contract_subst_imported_function_refs_ok >> simp[]) >>
  `subst_consts_stmts_mods (consts_env_mods mods) b = b` by
    (drule checked_linked_body_subst_fixed >> simp[]) >>
  qpat_x_assum `b = subst_consts_stmts_mods _ ss` kall_tac >>
  drule_then assume_tac (cj 2 qualified_body_custom_errors) >>
  `src = NONE ==> !name. ~MEM (StructDecl name []) tops` by
    (strip_tac >> drule_all linked_main_structs_nonempty >> simp[]) >>
  `?out. type_stmts env ret b = SOME out` by fs[optionTheory.IS_SOME_EXISTS] >>
  `supported_function_body tops vis args b` suffices_by
    simp[supported_function_body_def] >>
  irule (INST_TYPE [alpha |-> numSyntax.num] linked_typed_body_supported) >>
  conj_tac >- simp[] >>
  qexistsl_tac [`env`, `mods`, `out`, `ret`, `src`, `tenv`] >>
  conj_tac
  >- (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      drule linked_well_typed_expr_supported >>
      disch_then (qspec_then `tenv` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
      qpat_assum `!env e. well_typed_expr env e ==> _`
        (qspecl_then [`env'`, `e`] mp_tac) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >>
      rewrite_tac[subst_consts_stmt_mods_def, subst_consts_iter_mods_def] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      drule_all linked_checked_range_literals >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      drule_at (Pat `FDOM _ SUBSET _`) linked_checked_leaf >>
      disch_then (drule_at (Pat `type_stmt _ _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `linked_body_env _ _ _ _`)) >>
      disch_then (drule_at (Pat `custom_errors_stmt_ok _ _`)) >> simp[]) >>
  simp[]
QED

Theorem checked_linked_substituted_body_supported:
  check_contract F layouts addr mods = SOME art /\
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
  linked_body_env tops src tenv env /\
  FDOM env.var_types = set (MAP FST args) /\ ALL_DISTINCT (MAP FST args) /\
  b = subst_consts_stmts_mods (consts_env_mods mods) ss /\
  IS_SOME (type_stmts env ret b) /\ qualified_stmts_decls_ok mods b ==>
  supported_stmts tops (args ++ supported_stmts_bindings T b ++ supported_stmts_bindings F b) b
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule checked_linked_substituted_body_supported_mode >>
  simp[] >>
  metis_tac[]
QED
