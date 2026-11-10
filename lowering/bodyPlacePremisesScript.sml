(* Public body-level inputs to place assignment, independent of RHS layout. *)
Theory bodyPlacePremises
Ancestors
  bodyAugPlaceTarget bodySim bodyExprPreFacts bodyStorageCases bodyStorageMetadata
  stmtSimAssignPlace targetPlaceSim targetPlaceSimCases supportedStmts supportedTargets
  supportedDecls supportedExprForms supportedProgram supportedStmtTraverse supportedExprTraverse
  exprSimHypsDefs vyperTypeSystem vyperTypeInvariants gasContext
  vyperCompiler compileVyper stmtLowering exprLowering allocLimits
  vyperTypeCallGraph vyperTypeCallStackSoundness

Theorem legacy_storage_root_not_immutable[local]:
  body_inv tops ctx cenv cx /\
  (supported_scalar_target tops (src,id) \/
   supported_subscript_base tops (src,id) \/
   (?fld. supported_storage_field_write tops (src,id) fld)) ==>
  ~immutable_root cx (TopLevelNameTarget (src,id))
Proof
  strip_tac >>
  `get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  `src = NONE` by
    (Cases_on `src` >> gvs[supported_lookup_other_module,
         supported_scalar_target_def, supported_subscript_base_def,
         supported_storage_array_def, supported_storage_field_write_def,
         supported_storage_fields_def]) >>
  gvs[immutable_root_def, target_root_def] >>
  `IS_SOME (find_var_decl_by_name id tops)` suffices_by
    metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE] >>
  irule aug_place_supported_root_decl >>
  gvs[supported_scalar_target_def, supported_subscript_base_def,
      supported_storage_array_def, supported_storage_field_write_def,
      supported_storage_fields_def] >>
  Cases_on `supported_hashmap_decl tops (NONE,id)` >>
  simp[GSYM pairTheory.EXISTS_PROD] >>
  namedCases_on `supported_variable_decl tops (NONE,id)` ["", "decl"] >>
  gvs[] >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  gvs[] >> Cases_on `decl2` >> gvs[] >> metis_tac[]
QED

Theorem body_assignment_place_premises:
  body_expr_ok cx e /\ body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assign (BaseTarget t) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  expr_body_pre cenv cx env e es /\
  expr_vv_sim ctx func cenv cx (expr_type e) e es /\
  target_indices_pre cenv cx env t /\
  (body_base_target_ok cx t ==> target_case F ctx func cenv cx t) /\
  cenv.ce_target CapMcopy /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv t e /\
  ?dty. type_place_target env t = SOME (Type dty) /\
        type_widens_to env.type_defs (expr_type e) dty /\
        assignable_type env.type_defs (expr_type e) /\
        (immutable_root cx t ==>
          ?nsid. t = TopLevelNameTarget nsid /\
                 supported_immutable_type tops nsid = SOME dty /\ cx.in_deploy)
Proof
  strip_tac >>
  `well_typed_expr env e /\
   ?dty. type_place_target env t = SOME (Type dty) /\
         type_widens_to env.type_defs (expr_type e) dty /\
         assignable_type env.type_defs (expr_type e)` by
    (qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
     rpt strip_tac >> Cases_on `type_place_target env t` >> gvs[] >>
     rename1 `SOME pt` >> Cases_on `pt` >> gvs[]) >>
  conj_asm1_tac >- suspend "rhs" >>
  conj_tac >- metis_tac[body_expr_ok_def] >>
  conj_tac >- suspend "indices" >>
  conj_tac >- metis_tac[aug_place_body_target_idx, target_case_all] >>
  conj_tac >- suspend "mcopy" >>
  conj_tac >- gvs[body_inv_def] >>
  conj_tac >- fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  qexists_tac `dty` >> simp[] >> suspend "immutable"
QED

Resume body_assignment_place_premises[rhs]:
  `supported_expr tops e` by gvs[supported_stmt_def, supported_assignment_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by gvs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >> metis_tac[call_evaluation_safe_append_right]
QED

Resume body_assignment_place_premises[indices]:
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by gvs[body_inv_def] >>
  Cases_on `IS_SOME (supported_target_info tops bindings t)`
  >- (irule aug_place_target_indices_pre >>
      gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
          supported_assignment_exists_def, int_calls_stmt_def, int_calls_atarget_def] >>
      conj_tac >- metis_tac[] >>
      metis_tac[call_evaluation_safe_append_left]) >>
  `supported_target tops bindings t` by
    (gvs[supported_stmt_def, supported_assignment_def, AllCaseEqs()]) >>
  Cases_on `t` >> gvs[target_indices_pre_def]
  >- (rename1 `supported_target tops bindings (SubscriptTarget bt k)` >>
      Cases_on `bt` >> gvs[supported_target_def, target_indices_pre_def] >>
      suspend "legacy_index") >>
  rename1 `supported_target tops bindings (AttributeTarget bt fld)` >>
  Cases_on `bt` >> gvs[supported_target_def, target_indices_pre_def]
QED

Resume body_assignment_place_premises[legacy_index]:
  rpt strip_tac >>
  `well_typed_expr env k` by fs[Once well_typed_expr_def, AllCaseEqs()] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_expr_exists_def,
      int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Resume body_assignment_place_premises[mcopy]:
  qpat_x_assum `body_inv _ _ _ _` mp_tac >>
  rw[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
  >- (gvs[lower_vyper_deploy_unit_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[vyperCompilerTheory.run_deploy_lowering_def, AllCaseEqs(),
          vyperCompilerTheory.lowering_policy_ok_def]) >>
  gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperCompilerTheory.run_lowering_def, AllCaseEqs(),
      vyperCompilerTheory.lowering_policy_ok_def]
QED

Resume body_assignment_place_premises[immutable]:
  strip_tac >>
  `supported_target tops bindings t` by
    (gvs[supported_stmt_def, supported_assignment_def] >>
     Cases_on `supported_target_info tops bindings t` >>
     gvs[AllCaseEqs()] >>
     metis_tac[aug_place_supported_root_not_immutable]) >>
  `?nsid ity. t = TopLevelNameTarget nsid /\
              supported_immutable_type tops nsid = SOME ity` by
    (Cases_on `t` >> gvs[supported_target_def, immutable_root_def, target_root_def,
                              optionTheory.IS_SOME_EXISTS]
     >- metis_tac[legacy_storage_root_not_immutable,
                   immutable_root_def, target_root_def] >>
     Cases_on `b` >> gvs[supported_target_def, immutable_root_def, target_root_def] >>
     metis_tac[legacy_storage_root_not_immutable,
                              immutable_root_def, target_root_def]) >>
  gvs[] >> PairCases_on `nsid` >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (nsid0,nsid1)` >> simp[] >>
  rename1 `_ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac supported_variable_decl_mem >> gvs[] >>
  rename1 `supported_value_type tops ity` >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx /\
   bare_global_assignable_complete env.bare_global_assignable cx` by
    fs[body_inv_def, expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `FLOOKUP env.bare_globals (NONE,nsid1) = SOME ity` by
    metis_tac[bare_globals_complete_def] >>
  fs[Once well_typed_expr_def] >>
  Cases_on `cx.in_deploy`
  >- (`FLOOKUP env.bare_global_assignable (NONE,nsid1) = SOME ity` by
        metis_tac[bare_global_assignable_complete_def] >> fs[]) >>
  fs[bare_global_assignable_complete_def]
QED

Finalise body_assignment_place_premises
