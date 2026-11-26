(* Whitelist removal: a body the checker types is in the statement gate.

   The typing environment satisfies checker_env_ok (expressions) and
   checker_stmt_env_ok (assignable immutables, storage targets, events), and
   its variables are among the body's bindings. Range bounds read the
   constant-substituted body, which the checker types as well.

   TOP-LEVEL: checker_stmt_env_ok_def, type_stmts_supported (body safety
   follows from supported_stmts_body_safe in bodyExprPreFacts). *)
Theory whitelistCheckerStmts
Ancestors
  list pred_set finite_map alist pair vyperAST vyperValue vyperContext vyperTypeSystem
  vyperTypeCallGraph vyperEventArgCompat vyperTypeEnvExtension constSubst
  vyperTypeContract checkedTypeNamespace
  supportedTypes supportedDecls supportedExprForms supportedExprs
  supportedTargets supportedStmtTraverse supportedStmts
  whitelistCheckerDecls whitelistCheckerExprs supportedGetterProps
  whitelistStorageTargetProps
  whitelistIteratorProps whitelistStringReasonProps

(* ===== The statement environment ===== *)

Definition checker_stmt_env_ok_def:
  checker_stmt_env_ok tops env <=>
    (!k ty. FLOOKUP env.bare_global_assignable k = SOME ty ==>
       FLOOKUP env.bare_globals k = SOME ty /\ supported_place_root tops k /\
       supported_immutable_type tops k = SOME ty) /\
    (!k ty. FLOOKUP env.bare_globals k = NONE /\
            FLOOKUP env.toplevel_vtypes k = SOME (Type ty) ==>
       supported_storage_value tops k ty) /\
    (!id fields. FLOOKUP env.event_fields id = SOME fields ==>
       supported_event_fields tops id = SOME fields)
End

Theorem checker_stmt_env_ok_extend_local:
  checker_stmt_env_ok tops (extend_local env id ty b) <=>
  checker_stmt_env_ok tops env
Proof
  simp[checker_stmt_env_ok_def, extend_local_def]
QED

Theorem type_stmt_result_env[local]:
  type_stmt env ret s = SOME env' ==>
  env' = case s of AnnAssign id ty e => extend_local env id ty T | _ => env
Proof
  Cases_on `s` >>
  TRY (rename1 `Assert _ r` >> Cases_on `r`) >>
  TRY (rename1 `Raise r` >> Cases_on `r`) >>
  TRY (rename1 `Return r` >> Cases_on `r`) >>
  rw[type_stmt_def, AllCaseEqs()]
QED

Theorem type_stmt_checker_envs[local]:
  type_stmt env ret s = SOME env' /\ checker_env_ok tops env /\
  checker_stmt_env_ok tops env ==>
  checker_env_ok tops env' /\ checker_stmt_env_ok tops env' /\
  FDOM env'.var_types SUBSET
    FDOM env.var_types UNION set (MAP FST (supported_stmt_bindings T s))
Proof
  strip_tac >> drule type_stmt_result_env >> strip_tac >>
  Cases_on `s` >>
  gvs[supported_stmt_bindings_def, checker_stmt_env_ok_extend_local, SUBSET_DEF] >>
  conj_tac >- (irule checker_env_ok_extend_local >> fs[] >>
               `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
               gvs[type_stmt_def, AllCaseEqs()]) >>
  simp[extend_local_def] >> metis_tac[]
QED

(* ===== Expressions ===== *)

Theorem checker_pure[local]:
  checker_env_ok tops env /\ well_typed_expr env e ==>
  supported_pure_expr tops e
Proof
  metis_tac[well_typed_expr_supported]
QED

Theorem checker_supported_expr[local]:
  checker_env_ok tops env /\ well_typed_expr env e ==> supported_expr tops e
Proof
  metis_tac[checker_pure, supported_expr_def]
QED

Theorem checker_pures[local]:
  checker_env_ok tops env /\ well_typed_exprs env es ==>
  EVERY (supported_pure_expr tops) es
Proof
  metis_tac[well_typed_expr_supported]
QED

Theorem checker_string_reason[local]:
  checker_env_ok tops env /\ well_typed_expr env e /\
  expr_type e = BaseT (StringT n) ==>
  supported_string_reason tops e
Proof
  metis_tac[checker_pure, supported_string_reason_from_pure]
QED

(* ===== Targets ===== *)

Theorem checker_toplevel_target_root[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  type_place_target env (TopLevelNameTarget k) = SOME vt ==>
  supported_place_root tops k
Proof
  PairCases_on `k` >> rw[well_typed_expr_def, AllCaseEqs()] >>
  gvs[checker_stmt_env_ok_def] >>
  metis_tac[checker_toplevel_name_place]
QED

Theorem type_place_target_supported_info[local]:
  (!e:expr. T) /\
  !tgt vt. checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
    FDOM env.var_types SUBSET set (MAP FST bindings) /\
    type_place_target env tgt = SOME vt ==>
    IS_SOME (supported_target_info tops bindings tgt)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[]
  >~ [`NameTarget`]
  >- (gvs[well_typed_expr_def, AllCaseEqs(), SUBSET_DEF, FLOOKUP_DEF,
          supported_target_info_def] >>
      rename1 `ALOOKUP bindings nm` >>
      Cases_on `ALOOKUP bindings nm` >> gvs[ALOOKUP_NONE])
  >~ [`TopLevelNameTarget`]
  >- (drule_all checker_toplevel_target_root >> strip_tac >>
      drule supported_place_root_target_info >> simp[])
  >~ [`SubscriptTarget`]
  >- (qpat_x_assum `type_place_target _ _ = _` mp_tac >>
      simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      `supported_expr tops e` by metis_tac[checker_supported_expr] >>
      simp[supported_target_info_def] >> metis_tac[])
  >> gvs[well_typed_expr_def, AllCaseEqs(), supported_target_info_def] >>
  metis_tac[]
QED

Theorem type_place_target_supported_target[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  type_place_target env tgt = SOME (Type ty) ==>
  supported_target tops bindings tgt
Proof
  strip_tac >> Cases_on `tgt`
  >~ [`TopLevelNameTarget k`]
  >- (PairCases_on `k` >>
      gvs[well_typed_expr_def, AllCaseEqs(), supported_target_def]
      >~ [`FLOOKUP env.bare_global_assignable _ = SOME _`]
      >- (fs[checker_stmt_env_ok_def] >> res_tac >> simp[]) >>
      disj1_tac >> irule storage_value_scalar_target >> qexists_tac `ty` >>
      fs[checker_stmt_env_ok_def]) >>
  drule_all (cj 2 type_place_target_supported_info) >>
  simp[supported_target_def, supported_target_info_def] >>
  rename1 `ALOOKUP bindings nm` >> Cases_on `ALOOKUP bindings nm` >> simp[]
QED

Theorem tuple_targets_supported[local]:
  !l tys. checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
    FDOM env.var_types SUBSET set (MAP FST bindings) /\
    EVERY (\tgt. case tgt of BaseTarget _ => T | TupleTarget _ => F) l /\
    LIST_REL (\tgt ty. well_typed_atarget env tgt ty) l tys ==>
    EVERY (\g. case g of
             BaseTarget bt => supported_target tops bindings bt
           | TupleTarget _ => F) l
Proof
  Induct >> simp[LIST_REL_CONS1, PULL_EXISTS] >> Cases >>
  simp[well_typed_atarget_def, well_typed_target_def] >>
  metis_tac[type_place_target_supported_target]
QED

Theorem type_stmt_assign_supported[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  type_stmt env ret (Assign tgt e) = SOME env' ==>
  supported_assignment tops bindings tgt e
Proof
  strip_tac >> simp[supported_assignment_def] >> conj_tac
  >- (gvs[type_stmt_def, AllCaseEqs()] >> metis_tac[checker_supported_expr]) >>
  Cases_on `tgt` >> simp[]
  >- (drule type_stmt_assign_base_target_value >> strip_tac >>
      metis_tac[type_place_target_supported_target]) >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
      AllCaseEqs()] >>
  metis_tac[tuple_targets_supported]
QED

Theorem type_stmt_append_supported[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  type_stmt env ret (Append bt e) = SOME env' ==>
  supported_append_target tops bt /\ supported_pure_expr tops e
Proof
  rw[type_stmt_def, AllCaseEqs()] >~ [`supported_pure_expr _ _`]
  >- metis_tac[checker_pure] >>
  `EVERY (supported_pure_expr tops) (target_indices bt)`
    by (qspecl_then [`env`,`bt`] mp_tac (cj 3 well_typed_expr_supported) >> simp[]) >>
  Cases_on `bt` >> gvs[supported_append_target_def, target_indices_def] >>
  rename1 `TopLevelNameTarget k` >> PairCases_on `k` >>
  gvs[well_typed_expr_def, target_mutable_def, AllCaseEqs(),
      checker_stmt_env_ok_def] >>
  res_tac >> imp_res_tac storage_value_dynamic_array >> gvs[]
QED

Theorem type_stmt_augassign_supported[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  type_stmt env ret (AugAssign ty bt op e) = SOME env' ==>
  supported_stmt tops bindings (AugAssign ty bt op e)
Proof
  rw[type_stmt_def, supported_stmt_def, supported_binop_def,
     well_typed_target_def] >>
  metis_tac[type_place_target_supported_target, checker_supported_expr]
QED

(* ===== Logs and reasons ===== *)

Theorem type_stmt_log_supported_env[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  type_stmt env ret (Log id es) = SOME env' ==>
  supported_log tops id es
Proof
  rw[type_stmt_def, AllCaseEqs(), supported_log_def,
     supported_pure_exprs_every] >- metis_tac[checker_pures] >>
  fs[checker_stmt_env_ok_def] >> res_tac >> fs[event_arg_compatible_alias_def]
QED

(* ===== Iterators ===== *)

Theorem type_env_key_main:
  !tops id x. FLOOKUP (type_env tops) id = SOME x ==> FST id = NONE
Proof
  simp[type_env_def] >> Induct >> simp[type_env_for_module_def] >> Cases >>
  rw[type_env_for_module_def, FLOOKUP_UPDATE] >> res_tac >> gvs[]
QED

Theorem assignable_type_namespace[local]:
  !tenv ty. assignable_type tenv ty ==>
    (!id x. FLOOKUP tenv id = SOME x ==> FST id = NONE) ==>
    supported_type_namespace ty
Proof
  ho_match_mp_tac assignable_type_ind >>
  rw[assignable_type_def, supported_type_namespace_def,
     supported_types_namespace_every, EVERY_MEM] >>
  gvs[AllCaseEqs(), well_formed_type_def, evaluate_type_def] >>
  rename1 `supported_main_nsid nsid` >> PairCases_on `nsid` >>
  simp[supported_main_nsid_def] >>
  Cases_on `FLOOKUP tenv (nsid0,nsid1)` >> gvs[] >> res_tac >> gvs[]
QED

Theorem type_stmt_for_range_supported[local]:
  checker_env_ok tops env /\
  type_stmt env ret (For x ty (Range a b) n lbody) = SOME env' /\
  IS_SOME (type_stmt env ret
    (For x ty (Range (subst_consts_expr (module_consts_env tops []) a)
                     (subst_consts_expr (module_consts_env tops []) b)) n body2)) ==>
  supported_iterator tops ty (Range a b) n
Proof
  strip_tac >> irule typed_range_iterator_supported >> conj_tac
  >- (rpt strip_tac >> gvs[optionTheory.IS_SOME_EXISTS] >>
      drule type_stmt_for_range_literal_bounds >> rw[] >> intLib.ARITH_TAC) >>
  qexistsl [`env`, `lbody`, `env'`, `ret`, `x`] >>
  simp[] >> metis_tac[checker_pure]
QED

Theorem type_stmt_for_array_supported[local]:
  checker_env_ok tops env /\
  type_stmt env ret (For x ty (Array e) n lbody) = SOME env' ==>
  supported_iterator tops ty (Array e) n
Proof
  strip_tac >> irule typed_array_iterator_supported >>
  qexistsl [`env`, `lbody`, `env'`, `ret`, `x`] >>
  simp[] >> metis_tac[checker_pure]
QED

Theorem type_stmt_for_head_supported[local]:
  checker_env_ok tops env /\
  type_stmt env ret (For x ty it n lbody) = SOME env' /\
  IS_SOME (type_stmt env ret
    (subst_consts_stmt (module_consts_env tops []) (For x ty it n lbody))) ==>
  supported_type_namespace ty /\ supported_iterator tops ty it n /\
  checker_env_ok tops (extend_local env x ty F) /\
  IS_SOME (type_stmts (extend_local env x ty F) ret
    (subst_consts_stmts (module_consts_env tops []) lbody))
Proof
  strip_tac >>
  `env.type_defs = type_env tops` by fs[checker_env_ok_def] >>
  rpt conj_tac
  >- (gvs[type_stmt_def, AllCaseEqs()] >> drule assignable_type_namespace >>
      metis_tac[type_env_key_main])
  >- (Cases_on `it` >> fs[subst_consts_stmt_def, subst_consts_iter_def] >>
      metis_tac[type_stmt_for_array_supported, type_stmt_for_range_supported])
  >- (irule checker_env_ok_extend_local >> gvs[type_stmt_def, AllCaseEqs()]) >>
  gvs[subst_consts_stmt_def, type_stmt_def, AllCaseEqs()]
QED

Theorem type_stmt_cons_envs[local]:
  type_stmt env ret s = SOME e1 /\ checker_env_ok tops env /\
  checker_stmt_env_ok tops env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  set (MAP FST (supported_stmt_bindings T s)) SUBSET set (MAP FST bindings) ==>
  checker_env_ok tops e1 /\ checker_stmt_env_ok tops e1 /\
  FDOM e1.var_types SUBSET set (MAP FST bindings)
Proof
  strip_tac >> drule_all type_stmt_checker_envs >> fs[SUBSET_DEF] >> metis_tac[]
QED

(* ===== Statements ===== *)

Triviality checker_custom_error_supported:
  custom_error_resolved [(NONE,tops)] err ==> supported_custom_error tops err
Proof
  Cases_on `err` >> simp[supported_custom_error_def]
QED

Theorem type_stmt_leaf_supported[local]:
  checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
  FDOM env.var_types SUBSET set (MAP FST bindings) /\
  custom_errors_stmt_ok [(NONE, tops)] s /\
  type_stmt env ret s = SOME env' /\
  (!c yes no. s <> If c yes no) /\ (!x ty it n b. s <> For x ty it n b) ==>
  supported_stmt tops bindings s
Proof
  strip_tac >> Cases_on `s` >> gvs[]
  >~ [`Assign`] >- (simp[supported_stmt_def] >> metis_tac[type_stmt_assign_supported])
  >~ [`AugAssign`] >- metis_tac[type_stmt_augassign_supported]
  >~ [`Append`] >- (simp[supported_stmt_def] >> metis_tac[type_stmt_append_supported])
  >~ [`Log`] >- (simp[supported_stmt_def] >> metis_tac[type_stmt_log_supported_env])
  >~ [`AnnAssign`]
  >- (gvs[type_stmt_def, supported_stmt_def, AllCaseEqs()] >>
      metis_tac[checker_supported_expr, checker_env_ok_def,
                assignable_type_supported_place])
  >~ [`Assert _ r`]
  >- (Cases_on `r` >>
      gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(),
          supported_assert_reason_def,
          custom_errors_stmt_ok_def, well_typed_custom_error_def] >>
      metis_tac[checker_pure, checker_pures, checker_string_reason,
                checker_custom_error_supported])
  >~ [`Raise r`]
  >- (Cases_on `r` >>
      gvs[type_stmt_def, supported_stmt_def, AllCaseEqs(),
          supported_raise_reason_def,
          custom_errors_stmt_ok_def, well_typed_custom_error_def] >>
      metis_tac[checker_pures, checker_string_reason, checker_custom_error_supported])
  >~ [`Return r`]
  >- (Cases_on `r` >> gvs[type_stmt_def, supported_stmt_def, AllCaseEqs()] >>
      metis_tac[checker_supported_expr])
  >> gvs[type_stmt_def, supported_stmt_def, AllCaseEqs()] >>
  metis_tac[checker_supported_expr]
QED

Theorem type_stmts_supported:
  (!env ret s env'. type_stmt env ret s = SOME env' ==>
     checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
     FDOM env.var_types SUBSET set (MAP FST bindings) /\
     set (MAP FST (supported_stmt_bindings T s ++ supported_stmt_bindings F s))
       SUBSET set (MAP FST bindings) /\
     custom_errors_stmt_ok [(NONE, tops)] s /\
     IS_SOME (type_stmt env ret
       (subst_consts_stmt (module_consts_env tops []) s)) ==>
     supported_stmt tops bindings s) /\
  (!env ret ss env'. type_stmts env ret ss = SOME env' ==>
     checker_env_ok tops env /\ checker_stmt_env_ok tops env /\
     FDOM env.var_types SUBSET set (MAP FST bindings) /\
     set (MAP FST (supported_stmts_bindings T ss ++ supported_stmts_bindings F ss))
       SUBSET set (MAP FST bindings) /\
     custom_errors_stmts_ok [(NONE, tops)] ss /\
     IS_SOME (type_stmts env ret
       (subst_consts_stmts (module_consts_env tops []) ss)) ==>
     supported_stmts tops bindings ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY strip_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`supported_stmt _ _ (If _ _ _)`]
  >- (qpat_x_assum `IS_SOME (type_stmt _ _ (subst_consts_stmt _ _))` mp_tac >>
      gvs[type_stmt_def, AllCaseEqs(), subst_consts_stmt_def,
          supported_stmt_def, supported_stmt_bindings_def,
          custom_errors_stmt_ok_def, optionTheory.IS_SOME_EXISTS] >>
      metis_tac[checker_pure])
  >~ [`supported_stmt _ _ (For _ _ _ _ _)`]
  >- (drule_all type_stmt_for_head_supported >>
      gvs[supported_stmt_def, supported_stmt_bindings_def, custom_errors_stmt_ok_def,
          checker_stmt_env_ok_extend_local, optionTheory.IS_SOME_EXISTS, UNION_SUBSET] >>
      rpt strip_tac >> gvs[type_stmt_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS] >>
      first_x_assum irule >> simp[extend_local_def, INSERT_SUBSET])
  >~ [`supported_stmts _ _ (_ :: _)`]
  >- (qpat_x_assum `type_stmts _ _ (_::_) = _` mp_tac >>
      qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
      simp[type_stmt_def, subst_consts_stmt_def, AllCaseEqs(),
           optionTheory.IS_SOME_EXISTS, PULL_EXISTS] >>
      rpt strip_tac >> imp_res_tac type_stmt_subst_consts_result >> gvs[] >>
      fs[supported_stmt_def, supported_stmt_bindings_def,
         custom_errors_stmt_ok_def, UNION_SUBSET] >>
      drule_all type_stmt_cons_envs >> strip_tac >> fs[])
  >~ [`supported_stmts _ _ []`] >- simp[supported_stmt_def]
  >> irule type_stmt_leaf_supported >> simp[] >> metis_tac[]
QED
