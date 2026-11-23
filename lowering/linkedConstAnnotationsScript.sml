(* Qualified constant inlining preserves the checker annotation at the root. *)
Theory linkedConstAnnotations
Ancestors
  bodyQualifiedStmtSource constSubstMods constSubst vyperTypeContractStaticMaps
  vyperTypeConstantCells vyperTypeContractContext vyperTypeEventLookup vyperTypeEnvExtension
  vyperTypeContract vyperTypeSystem vyperInterpreter vyperContext vyperAST
  exprSimSource[qualified,ignore_grammar] alist pair list

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
    (qpat_x_assum `well_typed_expr env _` mp_tac >>
     simp[artifact_env_def, well_typed_expr_def]) >>
  `ALOOKUP ((initial_evaluation_context [(0w,mods)] []
     empty_call_txn NONE).sources)
     ((initial_evaluation_context [(0w,mods)] [] empty_call_txn NONE).txn).target =
       SOME mods` by
    simp[initial_evaluation_context_def, empty_call_txn_def, ALOOKUP_def] >>
  `MEM (id0,tops) mods` by (irule ALOOKUP_MEM >> simp[]) >>
  drule_all checked_constant_declared_type >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `!tl. MEM tl decls ==> ?tops. ALOOKUP mods src = SOME tops /\ MEM tl tops` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `!s name r. ALOOKUP (module_consts_env_mods src decls cenv) (s,name) = SOME r ==>
      ?tops vis init slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name (expr_type r) slot) tops` by
    (qpat_assum `!acc. (_ /\ _) ==> _` (qspec_then `cenv` mp_tac) >> simp[]) >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl vis mut id ty slot` >>
  Cases_on `mut` >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl vis (Constant init) id ty slot` >>
  `?tops. ALOOKUP mods src = SOME tops /\
    MEM (VariableDecl vis (Constant init) id ty slot) tops` by
    (qpat_assum `!tl. tl = _ \/ MEM tl decls ==> _` irule >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule_all check_contract_toplevel_decl_MEM_checked >>
  simp[check_toplevel_decl_def] >> strip_tac >>
  `expr_type (fold_const_expr (subst_consts_expr_mods cenv init)) = ty` by
    (qsuff_tac `expr_type (subst_consts_expr_mods cenv init) = expr_type init` >- simp[] >>
     drule checked_const_replacement_type >> disch_then irule >>
     simp[] >> qexists_tac `artifact_env art mods src` >> simp[artifact_env_def]) >>
  qabbrev_tac `new = fold_const_expr (subst_consts_expr_mods cenv init)` >>
  `!s name r. ALOOKUP (cenv ++ [((src,id),new)]) (s,name) = SOME r ==>
      ?tops vis init slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name (expr_type r) slot) tops` by
    (rpt gen_tac >> simp[ALOOKUP_APPEND] >>
     Cases_on `ALOOKUP cenv (s,name)` >> simp[ALOOKUP_def] >>
     rw[] >> metis_tac[]) >>
  qpat_assum `!acc. (_ /\ _) ==> _`
    (qspec_then `cenv ++ [((src,id),new)]` mp_tac) >> simp[]
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
  rpt gen_tac >> strip_tac >>
  `ALOOKUP mods q = SOME r` by
    (qpat_assum `!src tops. _ ==> _`
       (qspecl_then [`q`,`r`] mp_tac) >> simp[]) >>
  `!s name v. ALOOKUP (module_consts_env_mods q r cenv) (s,name) = SOME v ==>
      ?tops vis init slot. ALOOKUP mods s = SOME tops /\
        MEM (VariableDecl vis (Constant init) name (expr_type v) slot) tops` by
    (drule checked_module_const_replacements >>
     disch_then (qspecl_then [`q`,`r`,`cenv`] mp_tac) >> simp[]) >>
  qpat_assum `!acc. (_ /\ _) ==> _`
    (qspec_then `module_consts_env_mods q r cenv` mp_tac) >>
  simp[] >> metis_tac[]
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
  simp[consts_env_mods_def, consts_env_modules_order_eq] >>
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
  rpt gen_tac >> qid_spec_tac `params` >> Induct_on `kwargs`
  >- (Cases >> simp[order_custom_error_kwargs_def, subst_consts_expr_mods_def]) >>
  qx_gen_tac `kw` >> PairCases_on `kw` >> Cases
  >- simp[order_custom_error_kwargs_def, subst_consts_expr_mods_def] >>
  rename1 `order_custom_error_kwargs (param::ps) _` >> PairCases_on `param` >>
  rw[order_custom_error_kwargs_def, subst_consts_expr_mods_def] >>
  Cases_on `order_custom_error_kwargs ps kwargs` >> simp[]
QED

Triviality ordered_error_args_subst:
  order_custom_error_args params (subst_consts_error_mods cenv err) =
  OPTION_MAP (MAP (subst_consts_expr_mods cenv))
    (order_custom_error_args params err)
Proof
  `!es. subst_consts_exprs_mods cenv es = MAP (subst_consts_expr_mods cenv) es`
    by (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!fs. NULL (subst_consts_fields_mods cenv fs) = NULL fs` by
    (Cases >> simp[subst_consts_expr_mods_def] >>
     rename1 `subst_consts_fields_mods cenv (f::fs)` >>
     PairCases_on `f` >> simp[subst_consts_expr_mods_def]) >>
  Cases_on `err` >>
  rw[subst_consts_error_mods_def, order_custom_error_args_def,
     ordered_error_kwargs_subst, NULL_EQ]
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
  Cases_on `err` >> rename1 `custom_error_resolved mods (CustomError id pos kw)` >>
  PairCases_on `id` >> strip_tac >>
  qpat_x_assum `custom_error_resolved _ _` mp_tac >>
  simp[custom_error_resolved_def] >>
  Cases_on `ALOOKUP mods id0` >> simp[] >> rename1 `ALOOKUP mods id0 = SOME tops` >>
  Cases_on `lookup_custom_error_args_in id1 tops` >> simp[] >>
  rename1 `lookup_custom_error_args_in id1 tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError (id0,id1) pos kw)` >> simp[] >>
  rename1 `order_custom_error_args params _ = SOME es` >> strip_tac >>
  `MAP expr_type (MAP (subst_consts_expr_mods (consts_env_mods mods)) es) =
   MAP expr_type es` by
    (pure_rewrite_tac[MAP_MAP_o] >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
     drule order_custom_error_args_perm >>
     disch_then (mp_tac o MATCH_MP sortingTheory.PERM_MEM_EQ) >>
     strip_tac >>
     drule checked_linked_const_annotation >> disch_then irule >>
     qexists_tac `env` >> simp[] >>
     irule exprSimSourceTheory.well_typed_exprs_member >>
     qexists_tac `custom_error_exprs (CustomError (id0,id1) pos kw)` >>
     fs[well_typed_custom_error_def]) >>
  `order_custom_error_args params
      (subst_consts_error_mods (consts_env_mods mods) (CustomError (id0,id1) pos kw)) =
   SOME (MAP (subst_consts_expr_mods (consts_env_mods mods)) es)` by
    simp[ordered_error_args_subst] >>
  pop_assum (mp_tac o REWRITE_RULE [subst_consts_error_mods_def]) >>
  simp[subst_consts_error_mods_def, custom_error_resolved_def]
QED

Triviality checked_custom_errors_stmts_subst:
  (!env err.
    env.bare_globals = art.cta_bare_globals /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\
    well_typed_custom_error env err /\ custom_error_resolved mods err ==>
    custom_error_resolved mods (subst_consts_error_mods cenv err)) ==>
  (!env ret s env'.
    type_stmt env ret s = SOME env' /\
    env.bare_globals = art.cta_bare_globals /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\ custom_errors_stmt_ok mods s ==>
    custom_errors_stmt_ok mods (subst_consts_stmt_mods cenv s)) /\
  (!env ret ss env'.
    type_stmts env ret ss = SOME env' /\
    env.bare_globals = art.cta_bare_globals /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\ custom_errors_stmts_ok mods ss ==>
    custom_errors_stmts_ok mods (subst_consts_stmts_mods cenv ss))
Proof
  strip_tac >> ho_match_mp_tac type_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[custom_errors_stmt_ok_def, subst_consts_stmt_mods_def,
       subst_consts_rreason_mods_def, subst_consts_areason_mods_def]
  >- (simp[type_stmt_def] >> metis_tac[])
  >- (simp[type_stmt_def] >> metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `type_stmt _ _ (If _ _ _) = _` mp_tac >>
      simp[type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
      metis_tac[])
  >- (rpt strip_tac >>
      qpat_x_assum `type_stmt _ _ (For _ _ _ _ _) = _` mp_tac >>
      simp[type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
      strip_tac >>
      qpat_x_assum `!out. type_stmts _ _ _ = SOME out /\ _ ==> _` drule >>
      gvs[extend_local_def])
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
  `!env err.
    env.bare_globals = art.cta_bare_globals /\
    env.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\
    well_typed_custom_error env err /\ custom_error_resolved mods err ==>
    custom_error_resolved mods (subst_consts_error_mods (consts_env_mods mods) err)` by
    (rpt strip_tac >> drule_all checked_custom_error_subst >> simp[]) >>
  `custom_errors_stmts_ok mods
      (subst_consts_stmts_mods (consts_env_mods mods) ss)` by
    (drule checked_custom_errors_stmts_subst >>
     disch_then (qspecl_then [`env`,`ret`,`ss`] mp_tac o CONJUNCT2) >>
     disch_then drule >> simp[]) >>
  rename1 `type_stmts env ret (subst_consts_stmts_mods _ ss) = SOME inlined_out` >>
  drule checked_body_qualified_stmt_decls >> disch_then irule >> simp[] >>
  map_every qexists_tac [`env`,`inlined_out`,`ret`] >> simp[]
QED
