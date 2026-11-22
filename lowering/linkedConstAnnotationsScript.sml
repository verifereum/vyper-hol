(* Qualified constant inlining preserves the checker annotation at the root. *)
Theory linkedConstAnnotations
Ancestors
  bodyQualifiedStmtSource constSubstMods constSubst vyperTypeContractStaticMaps
  vyperTypeConstantCells vyperTypeContractContext vyperTypeEventLookup vyperTypeEnvExtension
  vyperTypeContract vyperTypeSystem vyperInterpreter vyperContext vyperAST
  alist pair list

Triviality checked_const_replacement_type:
  check_contract dep layouts addr mods = SOME art /\
  (!src name r. ALOOKUP consts (src,name) = SOME r ==>
    ?tops vis init ty slot.
      ALOOKUP mods src = SOME tops /\
      MEM (VariableDecl vis (Constant init) name ty slot) tops /\
      expr_type r = ty) /\
  env.bare_globals = art.cta_bare_globals /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env.type_defs = type_env_all_modules mods /\
  well_typed_expr env e ==>
  expr_type (subst_consts_expr_mods consts e) = expr_type e
Proof
  Cases_on `e` >> simp[subst_consts_expr_mods_def, expr_type_def] >>
  rename1 `well_typed_expr env (TopLevelName ann id)` >>
  PairCases_on `id` >> simp[subst_consts_expr_mods_def, expr_type_def] >>
  strip_tac >>
  Cases_on `ALOOKUP consts (id0,id1)` >> simp[expr_type_def] >>
  qpat_x_assum `!src name r. _`
    (qspecl_then [`id0`,`id1`,`x`] strip_assume_tac) >>
  gvs[] >>
  `well_typed_expr (artifact_env art mods NONE) (TopLevelName ann (id0,id1))` by
    fs[artifact_env_def, well_typed_expr_def] >>
  `ALOOKUP ((initial_evaluation_context [(0w,mods)] []
     empty_call_txn NONE).sources)
     ((initial_evaluation_context [(0w,mods)] [] empty_call_txn NONE).txn).target =
       SOME mods` by
    simp[initial_evaluation_context_def, empty_call_txn_def, ALOOKUP_def] >>
  drule_all (Q.INST
    [`cx` |-> `initial_evaluation_context [(0w,mods)] [] empty_call_txn NONE`]
    checked_constant_declared_type) >>
  simp[] >> metis_tac[ALOOKUP_MEM]
QED

Triviality checked_module_const_replacements:
  check_contract dep layouts addr mods = SOME art ==>
  !decls cenv.
    (!tl. MEM tl decls ==> ?tops. ALOOKUP mods src = SOME tops /\ MEM tl tops) /\
    (!s name r. ALOOKUP cenv (s,name) = SOME r ==>
      ?tops vis init ty slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name ty slot) tops /\ expr_type r = ty) ==>
    !s name r. ALOOKUP (module_consts_env_mods src decls cenv) (s,name) = SOME r ==>
      ?tops vis init ty slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name ty slot) tops /\ expr_type r = ty
Proof
  strip_tac >> Induct >> simp[module_consts_env_mods_def] >>
  Cases >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl vis mut id ty slot` >>
  Cases_on `mut` >> simp[module_consts_env_mods_def] >>
  rpt strip_tac >>
  rename1 `VariableDecl vis (Constant init) id ty slot` >>
  `?tops. ALOOKUP mods src = SOME tops /\
    MEM (VariableDecl vis (Constant init) id ty slot) tops` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  drule_all check_contract_toplevel_decl_MEM_checked >>
  simp[check_toplevel_decl_def] >> strip_tac >>
  `expr_type (fold_const_expr (subst_consts_expr_mods cenv init)) = ty` by
    (qsuff_tac `expr_type (subst_consts_expr_mods cenv init) = expr_type init` >- simp[] >>
     irule checked_const_replacement_type >>
     simp[artifact_env_def] >> metis_tac[]) >>
  first_x_assum irule >>
  simp[ALOOKUP_APPEND, ALOOKUP_def, AllCaseEqs()] >> metis_tac[]
QED

Triviality checked_const_replacements:
  check_contract dep layouts addr mods = SOME art ==>
  !units cenv.
    (!src tops. MEM (src,tops) units ==> ALOOKUP mods src = SOME tops) /\
    (!s name r. ALOOKUP cenv (s,name) = SOME r ==>
      ?tops vis init ty slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name ty slot) tops /\ expr_type r = ty) ==>
    !s name r. ALOOKUP (consts_env_mods_acc units cenv) (s,name) = SOME r ==>
      ?tops vis init ty slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name ty slot) tops /\ expr_type r = ty
Proof
  strip_tac >> Induct >> simp[consts_env_mods_acc_def] >>
  Cases >> simp[consts_env_mods_acc_def, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  drule checked_module_const_replacements >> metis_tac[]
QED

Triviality checked_linked_const_annotation:
  check_contract dep layouts addr mods = SOME art /\
  env.bare_globals = art.cta_bare_globals /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env.type_defs = type_env_all_modules mods /\
  well_typed_expr env e ==>
  expr_type (subst_consts_expr_mods (consts_env_mods mods) e) = expr_type e
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  irule checked_const_replacement_type >>
  simp[consts_env_mods_def] >>
  drule checked_const_replacements >>
  disch_then (qspecl_then [`constants_order mods`,`[]`] mp_tac) >>
  simp[MEM_constants_order, ALOOKUP_ALL_DISTINCT_MEM] >> metis_tac[]
QED

Triviality ordered_error_kwargs_subst:
  !params kwargs.
    order_custom_error_kwargs params (subst_consts_fields_mods cenv kwargs) =
    OPTION_MAP (MAP (subst_consts_expr_mods cenv))
      (order_custom_error_kwargs params kwargs)
Proof
  Induct >> Cases_on `kwargs` >>
  simp[order_custom_error_kwargs_def, subst_consts_expr_mods_def] >>
  PairCases_on `h` >> PairCases_on `h'` >>
  rw[order_custom_error_kwargs_def, subst_consts_expr_mods_def] >>
  Cases_on `order_custom_error_kwargs params t` >> simp[]
QED

Triviality ordered_error_args_subst:
  order_custom_error_args params (subst_consts_error_mods cenv err) =
  OPTION_MAP (MAP (subst_consts_expr_mods cenv))
    (order_custom_error_args params err)
Proof
  `!es. subst_consts_exprs_mods cenv es = MAP (subst_consts_expr_mods cenv) es`
    by (Induct >> simp[subst_consts_expr_mods_def]) >>
  Cases_on `err` >> Cases_on `l` >> Cases_on `l0` >>
  simp[subst_consts_error_mods_def, order_custom_error_args_def,
       subst_consts_expr_mods_def, ordered_error_kwargs_subst]
QED

Triviality checked_custom_error_subst:
  check_contract dep layouts addr mods = SOME art /\
  env.bare_globals = art.cta_bare_globals /\
  env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env.type_defs = type_env_all_modules mods /\
  well_typed_custom_error env err /\ custom_error_resolved mods err ==>
  custom_error_resolved mods
    (subst_consts_error_mods (consts_env_mods mods) err)
Proof
  Cases_on `err` >> PairCases_on `n` >>
  simp[custom_error_resolved_def, well_typed_custom_error_def] >>
  rpt strip_tac >>
  Cases_on `ALOOKUP mods n0` >> gvs[] >>
  Cases_on `lookup_custom_error_args_in n1 x` >> gvs[] >>
  Cases_on `order_custom_error_args x' (CustomError (n0,n1) l l0)` >> gvs[] >>
  drule order_custom_error_args_perm >> strip_tac >>
  `!e. MEM e x'' ==> well_typed_expr env e` by
    metis_tac[well_typed_exprs_def, PERM_MEM_EQ] >>
  simp[GSYM subst_consts_error_mods_def, ordered_error_args_subst] >>
  simp[MAP_MAP_o, o_DEF] >>
  irule MAP_CONG >> simp[] >> metis_tac[checked_linked_const_annotation]
QED

Triviality checked_custom_errors_stmts_subst:
  check_contract dep layouts addr mods = SOME art ==>
  (!env ret s env'.
    type_stmt env ret s = SOME env' /\
    env.bare_globals = art.cta_bare_globals /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\ custom_errors_stmt_ok mods s ==>
    custom_errors_stmt_ok mods (subst_consts_stmt_mods (consts_env_mods mods) s)) /\
  (!env ret ss env'.
    type_stmts env ret ss = SOME env' /\
    env.bare_globals = art.cta_bare_globals /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\ custom_errors_stmts_ok mods ss ==>
    custom_errors_stmts_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss))
Proof
  strip_tac >> ho_match_mp_tac type_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[custom_errors_stmt_ok_def, subst_consts_stmt_mods_def]
  >- (Cases_on `err` >>
      simp[type_stmt_def, custom_errors_stmt_ok_def, subst_consts_rreason_mods_def] >>
      metis_tac[checked_custom_error_subst])
  >- (Cases_on `err` >>
      simp[type_stmt_def, custom_errors_stmt_ok_def, subst_consts_areason_mods_def] >>
      metis_tac[checked_custom_error_subst])
  >- (rpt strip_tac >>
      qpat_x_assum `type_stmt _ _ (If _ _ _) = _` mp_tac >>
      simp[type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
      metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `type_stmt _ _ (For _ _ _ _ _) = _` mp_tac >>
      simp[type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS,
           extend_local_def] >>
      metis_tac[])
  >> rpt strip_tac >> Cases_on `type_stmt env ret s` >>
  gvs[type_stmt_def] >>
  drule type_stmt_preserve_nonlocal_fields >> metis_tac[]
QED

Theorem checked_qualified_body_decl_resolution:
  check_contract dep layouts addr mods = SOME art /\
  check_function_body layouts addr mods art src vis mut nr args dflts ret ss ==>
  qualified_stmts_decls_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss)
Proof
  simp[check_function_body_def, LET_THM, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  qabbrev_tac `env = function_entry_env art mods src vis args` >>
  `env.bare_globals = art.cta_bare_globals /\
   env.toplevel_vtypes = art.cta_toplevel_vtypes /\
   env.type_defs = type_env_all_modules mods /\
   env.event_fields = art.cta_event_fields` by
    simp[Abbr `env`, function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static] >>
  drule_then assume_tac (cj 2 (UNDISCH checked_custom_errors_stmts_subst)) >>
  metis_tac[checked_body_qualified_stmt_decls]
QED
