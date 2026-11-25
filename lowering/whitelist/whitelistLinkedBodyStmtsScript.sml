Theory whitelistLinkedBodyStmts
Ancestors
  list pred_set finite_map vyperAST vyperTypeSystem vyperTypeEnvExtension
  vyperImportRefs vyperTypeContract constSubst constSubstMods
  supportedTypes supportedDecls supportedExprs supportedStmtTraverse
  supportedStmts supportedProgram bodyExprPreFacts whitelistCheckerDecls
  whitelistLinkedBodyEnv bodyFullForFacts
  whitelistIteratorProps

Triviality linked_subst_stmt_same_scope:
  type_stmt env ret s = SOME out /\
  type_stmt env ret (subst_consts_stmt_mods E s) = SOME out' ==>
  out' = out
Proof
  Cases_on `s` >>
  TRY (rename1 `Return oexp` >> Cases_on `oexp`) >>
  TRY (rename1 `Raise r` >> Cases_on `r`) >>
  TRY (rename1 `Assert _ r` >> Cases_on `r`) >>
  rw[subst_consts_stmt_mods_def, type_stmt_def, AllCaseEqs()] >>
  gvs[subst_consts_rreason_mods_def, subst_consts_error_mods_def,
      subst_consts_areason_mods_def, subst_consts_expr_mods_def,
      Once type_stmt_def, AllCaseEqs()]
QED

Triviality linked_stmt_continue_scope:
  type_stmt env ret s = SOME out /\ linked_body_env tops src tenv env /\
  FDOM env.var_types SUBSET B /\
  set (MAP FST (supported_stmt_bindings T s)) SUBSET B ==>
  linked_body_env tops src tenv out /\ FDOM out.var_types SUBSET B
Proof
  Cases_on `s` >>
  TRY (rename1 `Return oexp` >> Cases_on `oexp`) >>
  TRY (rename1 `Raise r` >> Cases_on `r`) >>
  TRY (rename1 `Assert _ r` >> Cases_on `r`) >>
  rw[Once type_stmt_def, supported_stmt_bindings_def, AllCaseEqs()] >>
  gvs[]
  >- (irule linked_body_env_extend_local >> fs[linked_body_env_def] >> metis_tac[]) >>
  simp[extend_local_def, INSERT_SUBSET]
QED

(* The three premises are the independent leaf rules. The induction only
   threads lexical scopes and the two typings through the statement tree. *)
Triviality linked_typed_stmts_supported:
  (!env e. linked_body_env tops src tenv env /\
           (src = NONE \/ imported_expr_refs_ok e) /\
           well_typed_expr env e ==> supported_pure_expr tops e) ==>
  (!env ret s out. linked_body_env tops src tenv env /\
                   (src = NONE \/ imported_stmt_refs_ok s) /\
                   FDOM env.var_types SUBSET set (MAP FST bindings) /\
                   custom_errors_stmt_ok mods s /\ type_stmt env ret s = SOME out /\
                   (!c yes no. s <> If c yes no) /\
                   (!x ty it n b. s <> For x ty it n b) ==>
                   supported_stmt tops bindings s) ==>
  (!env ret x ty a b n lbody out ta i tb j.
    (src = NONE \/ imported_expr_refs_ok a /\ imported_expr_refs_ok b) /\
    type_stmt env ret (For x ty (Range a b) n lbody) = SOME out /\
    IS_SOME (type_stmt env ret
      (subst_consts_stmt_mods (consts_env_mods mods) (For x ty (Range a b) n lbody))) /\
    subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
    subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j) ==>
    i <= j /\ n = Num (j - i)) ==>
  (!env ret s out. type_stmt env ret s = SOME out ==>
     linked_body_env tops src tenv env /\
     (src = NONE \/ imported_stmt_refs_ok s) /\
     FDOM env.var_types SUBSET set (MAP FST bindings) /\
     set (MAP FST (supported_stmt_bindings T s ++ supported_stmt_bindings F s))
       SUBSET set (MAP FST bindings) /\
     custom_errors_stmt_ok mods s /\
     IS_SOME (type_stmt env ret (subst_consts_stmt_mods (consts_env_mods mods) s)) ==>
     supported_stmt tops bindings s) /\
  (!env ret ss out. type_stmts env ret ss = SOME out ==>
     linked_body_env tops src tenv env /\
     (src = NONE \/ imported_stmts_refs_ok ss) /\
     FDOM env.var_types SUBSET set (MAP FST bindings) /\
     set (MAP FST (supported_stmts_bindings T ss ++ supported_stmts_bindings F ss))
       SUBSET set (MAP FST bindings) /\
     custom_errors_stmts_ok mods ss /\
     IS_SOME (type_stmts env ret (subst_consts_stmts_mods (consts_env_mods mods) ss)) ==>
     supported_stmts tops bindings ss)
Proof
  ntac 3 disch_tac >>
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >>
  rpt (gen_tac ORELSE disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac))
  >~ [`supported_stmt _ _ (If _ _ _)`]
  >- (qpat_x_assum `IS_SOME (type_stmt _ _ (subst_consts_stmt_mods _ _))` mp_tac >>
      gvs[type_stmt_def, AllCaseEqs(), subst_consts_stmt_mods_def,
          supported_stmt_def, supported_stmt_bindings_def,
          custom_errors_stmt_ok_def, imported_stmt_refs_ok_def,
          optionTheory.IS_SOME_EXISTS, UNION_SUBSET] >>
      strip_tac >> rpt conj_tac >> metis_tac[])
  >~ [`supported_stmt _ _ (For _ _ _ _ _)`]
  >- (simp[supported_stmt_def] >> conj_tac
      >- (Cases_on `it`
          >- (irule typed_array_iterator_supported >> simp[PULL_EXISTS] >>
              fs[imported_stmt_refs_ok_def, imported_iterator_refs_ok_def] >>
              metis_tac[]) >>
          irule typed_range_iterator_supported >> simp[PULL_EXISTS] >>
          fs[imported_stmt_refs_ok_def, imported_iterator_refs_ok_def] >>
          metis_tac[]) >>
      qpat_x_assum `type_stmt _ _ (For _ _ _ _ _) = _`
        (strip_assume_tac o MATCH_MP type_stmt_for_projection) >>
      qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
      simp[subst_consts_stmt_mods_def, optionTheory.IS_SOME_EXISTS] >>
      disch_then (qx_choose_then `sub_out`
        (strip_assume_tac o MATCH_MP type_stmt_for_projection)) >>
      `linked_body_env tops src tenv (extend_local env id typ F)` by
        (irule linked_body_env_extend_local >> fs[linked_body_env_def] >> metis_tac[]) >>
      fs[supported_stmt_bindings_def, custom_errors_stmt_ok_def,
         imported_stmt_refs_ok_def, LEFT_OR_OVER_AND, UNION_SUBSET, INSERT_SUBSET,
         optionTheory.IS_SOME_EXISTS] >>
      first_x_assum irule >> simp[extend_local_def, INSERT_SUBSET] >> metis_tac[])
  >~ [`supported_stmts _ _ (_ :: _)`]
  >- (qpat_x_assum `type_stmts _ _ (_::_) = _` mp_tac >>
      qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
      simp[type_stmt_def, subst_consts_stmt_mods_def, AllCaseEqs(),
           optionTheory.IS_SOME_EXISTS, PULL_EXISTS] >>
      rpt strip_tac >> imp_res_tac linked_subst_stmt_same_scope >> gvs[] >>
      fs[supported_stmt_def, supported_stmt_bindings_def,
         custom_errors_stmt_ok_def, imported_stmt_refs_ok_def, UNION_SUBSET] >>
      drule_all linked_stmt_continue_scope >> strip_tac >>
      rpt conj_tac >> metis_tac[])
  >~ [`supported_stmts _ _ []`] >- simp[supported_stmt_def]
  >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem linked_typed_body_supported:
  (!env e. linked_body_env tops src tenv env /\
           (src = NONE \/ imported_expr_refs_ok e) /\
           well_typed_expr env e ==> supported_pure_expr tops e) /\
  (!env ret s out. linked_body_env tops src tenv env /\
                   (src = NONE \/ imported_stmt_refs_ok s) /\
                   FDOM env.var_types SUBSET
                     set (MAP FST (args ++ supported_stmts_bindings T ss ++
                                   supported_stmts_bindings F ss)) /\
                   custom_errors_stmt_ok mods s /\ type_stmt env ret s = SOME out /\
                   (!c yes no. s <> If c yes no) /\
                   (!x ty it n b. s <> For x ty it n b) ==>
                   supported_stmt tops (args ++ supported_stmts_bindings T ss ++
                                        supported_stmts_bindings F ss) s) /\
  (!env ret x ty a b n lbody out ta i tb j.
    (src = NONE \/ imported_expr_refs_ok a /\ imported_expr_refs_ok b) /\
    type_stmt env ret (For x ty (Range a b) n lbody) = SOME out /\
    IS_SOME (type_stmt env ret
      (subst_consts_stmt_mods (consts_env_mods mods) (For x ty (Range a b) n lbody))) /\
    subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
    subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j) ==>
    i <= j /\ n = Num (j - i)) /\
  linked_body_env tops src tenv env /\
  (src = NONE \/ imported_stmts_refs_ok ss) /\
  FDOM env.var_types = set (MAP FST args) /\ ALL_DISTINCT (MAP FST args) /\
  type_stmts env ret ss = SOME out /\
  IS_SOME (type_stmts env ret (subst_consts_stmts_mods (consts_env_mods mods) ss)) /\
  custom_errors_stmts_ok mods ss ==>
  supported_function_body tops vis args ss
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule (cj 2 type_stmt_bindings_fresh) >> disch_then assume_tac >>
  qabbrev_tac `bindings = args ++ supported_stmts_bindings T ss ++
                            supported_stmts_bindings F ss` >>
  `FDOM env.var_types SUBSET set (MAP FST bindings) /\
   set (MAP FST (supported_stmts_bindings T ss ++ supported_stmts_bindings F ss))
     SUBSET set (MAP FST bindings)` by
    (simp[Abbr `bindings`, SUBSET_DEF] >> metis_tac[]) >>
  `supported_stmts tops bindings ss` by
    (drule linked_typed_stmts_supported >> disch_then drule >> disch_then drule >>
     strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `body_stmts_safe tops ss` by metis_tac[supported_stmts_body_safe] >>
  gvs[supported_function_body_def, EVERY_MEM, Abbr `bindings`]
QED
