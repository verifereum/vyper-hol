(* Assign-specific scalar storage metadata and RHS boundary. *)
Theory bodyFullAssignToplevelSetup
Ancestors
  augAssignPtrToplevelMetadata bodyStorageMetadata bodyExprPreFacts bodySim
  bodyTypedTargetScope bodySingletonCallSupport
  supportedDecls bodyInvCodeProps bodyInvMetadataProps
  bodyMainModuleProps linkedStorageMetadataProps exprBodyPreProps bodyInvSplit alist compileUnit
  exprSimHypsDefs exprSimHyps supportedStmts supportedExprs supportedExprForms
  supportedStmtTraverse supportedExprTraverse vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperTypeContractStaticMaps compileEnv compileVyper
  vyperContext vyperState vyperAST finite_map list
  exprSimSource vyperTypeCallGraph gasContext allocLimits

Theorem body_assign_toplevel_word_full_setup_mods:
  contract_inv mods exps ctx cenv cx /\
  supported_stmt (main_module mods) bindings
    (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e) ==>
    occurs_abi_decode_target target (main_module mods)) /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e) /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget (NONE,id))) e)) /\
  supported_scalar_target (main_module mods) (NONE,id) /\
  (?dty. type_place_target env (TopLevelNameTarget (NONE,id)) = SOME (Type dty) /\
         is_word_type dty) ==>
  expr_body_pre_mods mods cenv cx env e es /\
  ?tr slot tvt.
    get_module_code cx NONE = SOME (main_module mods) /\
    find_var_decl_by_name id (main_module mods) = SOME (StorageVarDecl tr (expr_type e),id) /\
    lookup_var_slot_from_layout cx tr NONE id = SOME slot /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    cenv.ce_hashmap_info (NONE,id) = NONE /\
    cenv.ce_module_var_type (NONE,id) = SOME (expr_type e) /\
    is_word_type (expr_type e)
Proof
  strip_tac >>
  `supported_expr (main_module mods) e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) dty` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `~supported_expr_exists (const_name_root_mods mods) e` by
    (drule stmt_exprs_ok_module_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_assignment_exists_def]) >>
  `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `~is_extcode e` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
  conj_tac
  >- (mp_tac (Q.INST [`calls` |-> `[]`] stmt_expr_body_pre_main_mods) >>
      fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, supported_assignment_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def]) >>
  drule_then assume_tac contract_inv_main_module >>
  `get_module_code cx NONE = SOME (main_module mods)` by metis_tac[contract_inv_module_codes] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `find_var_decl_by_name id (main_module mods) <> NONE` by
    metis_tac[supported_scalar_target_decl, find_var_decl_storage_some] >>
  drule_all compileEnvTheory.type_widens_to_word >> strip_tac >>
  gvs[type_place_target_TopLevelNameTarget]
  >- (drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac body_inv_storage_var_types_mods >>
  drule find_var_decl_storage_mem >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS]
QED

Theorem body_assign_toplevel_word_full_setup:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
  supported_scalar_target tops nsid /\
  (?dty. type_place_target env (TopLevelNameTarget nsid) = SOME (Type dty) /\
         is_word_type dty) ==>
  expr_body_pre cenv cx env e es /\
  ?id tr slot tvt.
    nsid = (NONE,id) /\ get_module_code cx NONE = SOME tops /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr (expr_type e),id) /\
    lookup_var_slot_from_layout cx tr NONE id = SOME slot /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    cenv.ce_hashmap_info nsid = NONE /\
    cenv.ce_module_var_type nsid = SOME (expr_type e) /\
    is_word_type (expr_type e)
Proof
  Cases_on `nsid` >> rename1 `(src,id)` >> strip_tac >>
  `src = NONE` by metis_tac[body_inv_toplevel_target_main, optionTheory.IS_SOME_EXISTS] >>
  gvs[] >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_assignment_exists_def]) >>
  drule_all_then assume_tac expr_sim_inv_no_unallocated_bare_globals >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env es` by fs[expr_sim_inv_split_def] >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`]
    body_assign_toplevel_word_full_setup_mods) >>
  impl_tac >- (simp[main_module_def, ALOOKUP_def] >> metis_tac[]) >>
  simp[main_module_def, ALOOKUP_def] >> strip_tac >>
  drule_then assume_tac contract_inv_type_env >>
  fs[expr_body_pre_split_def, vyperContextTheory.type_env_all_modules_def,
     vyperContextTheory.type_env_def, finite_mapTheory.FUNION_FEMPTY_2,
     supported_stmt_expr_exists_def, supported_assignment_exists_def] >>
  metis_tac[body_inv_typed_calls_main, expr_body_pre_mods_well_typed]
QED
