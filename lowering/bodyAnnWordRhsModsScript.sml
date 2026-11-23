Theory bodyAnnWordRhsMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodySimDeclCases bodyInvariantFrameProps
  bodyInvCodeProps bodyInvExecutionProps bodyInvMetadataProps bodyExprPreFacts
  exprBodyPreProps exprSimSource exprSimHypsDefs exprSafeOperand placeTypingProps stmtSimProps
  vyperInterpreter vyperState vyperTypeCallStackSoundness allocLimitsProps
  supportedStmts supportedStmtTraverse supportedExprTraverse allocLimits
  vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  compileEnv stmtLowering finite_map

Theorem annassign_declare_rhs_inv[local]:
  expr_sim_inv_mods mods cenv cx env es /\ id NOTIN FDOM env.var_types /\
  declare_local cenv id typ sa = (ce,r) /\ cenv.ce_alloca_locals ==>
  expr_sim_inv_mods mods ce cx env es /\ ce.ce_module_vars = cenv.ce_module_vars
Proof
  strip_tac >> drule_all_then strip_assume_tac declare_local_ptr >>
  `ce.ce_var_type = (id =+ SOME typ) cenv.ce_var_type` by
    (qpat_x_assum `declare_local _ _ _ _ = _` mp_tac >>
     simp[declare_local_def, fresh_var_def, comp_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  `ce.ce_flag_member_id = cenv.ce_flag_member_id /\
   ce.ce_flag_n_members = cenv.ce_flag_n_members /\
   ce.ce_struct_fields = cenv.ce_struct_fields /\
   ce.ce_hashmap_info = cenv.ce_hashmap_info /\
   ce.ce_module_var_type = cenv.ce_module_var_type /\
   ce.ce_module = cenv.ce_module /\ ce.ce_modules = cenv.ce_modules /\
   ce.ce_module_vars = cenv.ce_module_vars /\
   ce.ce_func_return_type = cenv.ce_func_return_type /\
   ce.ce_is_ctor = cenv.ce_is_ctor /\ ce.ce_method_id = cenv.ce_method_id` by
    (qpat_assum `_ with <|ce_vars := _; ce_var_type := _;
                         ce_dynarray_capacity := _|> = cenv`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `place_map_tables_agree_on_defined ce env <=>
   place_map_tables_agree_on_defined cenv env` by
    (irule place_map_tables_agree_on_defined_cong >> simp[]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> n <> id` by
    (rpt strip_tac >> gvs[FLOOKUP_DEF]) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==>
     ?p sz. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) sz)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!n t. FLOOKUP env.var_types n = SOME t ==> n <> id`
       (drule_then assume_tac) >>
     qpat_assum `!n t. FLOOKUP env.var_types n = SOME t ==> ?p sz. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!n. n <> id ==> FLOOKUP ce.ce_vars n = _` (drule_then SUBST1_TAC) >>
     metis_tac[]) >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> ce.ce_var_type n = SOME t` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!n t. FLOOKUP env.var_types n = SOME t ==> n <> id`
       (drule_then assume_tac) >>
     qpat_assum `!n t. FLOOKUP env.var_types n = SOME t ==> cenv.ce_var_type n = SOME t`
       (drule_then assume_tac) >>
     `id <> n` by metis_tac[] >>
     asm_rewrite_tac[combinTheory.APPLY_UPDATE_THM, COND_CLAUSES]) >>
  asm_rewrite_tac[expr_sim_inv_mods_def]
QED

Theorem annassign_word_source_facts[local]:
  expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\ is_word_type typ ==>
  well_typed_expr env e /\ expr_type e = typ /\ id NOTIN FDOM env.var_types /\
  FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  ?tyv. evaluate_type (get_tenv cx) typ = SOME tyv
Proof
  strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> goal_assum (drule_at (Pat `type_stmt _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `well_typed_expr env e /\ expr_type e = typ /\ id NOTIN FDOM env.var_types` by
    (qpat_assum `type_stmt _ _ _ = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [Once type_stmt_def, AllCaseEqs()]) >>
     irule_at Any compileEnvTheory.type_widens_to_word >>
     qexists_tac `env.type_defs` >> simp[]) >>
  drule_then assume_tac expr_sim_inv_mods_env >> simp[] >> conj_tac
  >- (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
      fs[env_consistent_def, env_scopes_consistent_def, FLOOKUP_DEF] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `!n t. FLOOKUP env.var_types n = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, env_consistent_var_type_evaluates] >>
  drule_all well_typed_expr_type_well_formed >>
  simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem annassign_word_declared_rhs_mods:
  (!tenv s'' tyv t.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==> body_expr_full_ok_mods mods exps cx e) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (AnnAssign id typ e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (AnnAssign id typ e)) /\
  is_word_type typ ==>
  expr_type e = typ /\ cenv.ce_alloca_locals /\ FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  (?tyv. evaluate_type (get_tenv cx) typ = SOME tyv) /\
  (!sa ce r. declare_local cenv id typ sa = (ce,r) ==>
    expr_body_pre_mods mods ce cx env e es /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx typ e es)
Proof
  strip_tac >> drule_all_then strip_assume_tac annassign_word_source_facts >>
  drule_then assume_tac contract_inv_alloca_locals >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `same_frame cenv ce` by (drule_then irule declare_local_same_frame >> simp[]) >>
  drule_all_then strip_assume_tac annassign_declare_rhs_inv >>
  `contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx` by
    metis_tac[body_invariants_same_frame] >>
  `stmt_exprs_ok ce (AnnAssign id typ e)` by metis_tac[annassign_declare_exprs_ok] >>
  `expr_body_pre_mods mods ce cx env e es` by
    (drule_at_then (Pat `contract_inv _ _ _ ce _`) assume_tac contract_inv_cenv_modules >>
     drule_then assume_tac contract_inv_type_env >>
     `~expr_has_evm_run e` by
       (irule supported_expr_no_evm_run >> qexists_tac `tops` >>
        fs[Once supported_stmt_def]) >>
     qpat_x_assum `stmt_exprs_ok ce _` mp_tac >>
     simp[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, alloc_limits_stmt_def] >>
     strip_tac >> drule_then assume_tac alloc_limits_expr_not_extcode >>
     irule stmt_expr_body_pre_mods >>
     fs[int_calls_stmt_def, supported_stmt_expr_exists_def] >> conj_tac
     >- (`unallocated_bare_global_root ce env = unallocated_bare_global_root cenv env` by
           (simp[FUN_EQ_THM] >> Cases >> simp[unallocated_bare_global_root_def]) >> simp[]) >>
     qexists_tac `[]` >> simp[]) >>
  `body_expr_full_ok_mods mods exps cx e` by
    (first_x_assum irule >> qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!DF lo d PG src tops ctx sc f sf ce env ty es.
              _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!DF lo d PG f sf ty.
     expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[]
QED
