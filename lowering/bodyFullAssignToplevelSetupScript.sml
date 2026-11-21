(* Assign-specific scalar storage metadata and RHS boundary. *)
Theory bodyFullAssignToplevelSetup
Ancestors
  augAssignPtrToplevelMetadata bodyStorageMetadata bodyExprPreFacts bodySim
  bodyMemAssignTopCopyFacts supportedDecls
  exprSimHypsDefs exprSimHyps supportedStmts supportedExprs supportedExprForms
  supportedStmtTraverse supportedExprTraverse vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperTypeContractStaticMaps compileEnv compileVyper
  vyperContext vyperState vyperAST finite_map list
  exprSimSource vyperTypeCallGraph gasContext

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
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[topcopy_rhs_pre_supported] >>
  `?vis mut decl_ty slot.
    supported_variable_decl tops (src,id) = SOME (vis,mut,decl_ty,SOME slot) /\
    (mut = Storage \/ mut = Transient)` by
    (qpat_assum `supported_scalar_target tops _` mp_tac >>
     simp[NoAsms,supported_scalar_target_def] >>
     Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
     PairCases_on `x` >> Cases_on `x3` >> Cases_on `x1` >> simp[]) >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[find_var_decl_storage_some] >>
  `type_widens_to env.type_defs (expr_type e) dty` by
    fs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  drule_all type_widens_to_word >> strip_tac >>
  gvs[type_place_target_TopLevelNameTarget] >>
  TRY (drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[] >> NO_TAC) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `decl_ty = expr_type e` by metis_tac[build_maps_variable,optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS]
QED
