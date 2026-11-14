(* Assign-specific scalar storage metadata and RHS boundary. *)
Theory bodyFullAssignToplevelSetup
Ancestors
  augAssignPtrToplevelMetadata bodyStorageMetadata bodyExprPreFacts bodySim
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
  supported_scalar_target tops nsid ==>
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
  Cases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >> strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `supported_program tops /\ get_module_code cx NONE = SOME tops` by
       gvs[body_inv_def] >>
     `cx_tops cx = tops` by simp[cx_tops_def] >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
       supported_assignment_exists_def, int_calls_stmt_def,
       int_calls_atarget_def, int_calls_expr_def] >>
     conj_tac >- fs[body_inv_def] >> qexists_tac `[]` >> simp[]) >>
  simp[] >> drule augassign_supported_scalar_target_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[type_place_target_TopLevelNameTarget]
  >- (drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >> gvs[] >>
  drule_all type_widens_to_word >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED
