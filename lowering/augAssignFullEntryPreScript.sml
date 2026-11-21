(* Source-side preconditions for finite-horizon AugAssign composition. *)
Theory augAssignFullEntryPre
Ancestors vyperTypeEnv compileEnv targetPlaceSimCasesBase
  bodyAugPlaceTarget bodyExprPreFacts bodyStorageCases stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory
  bodySim exprSimHypsDefs targetPlaceSim targetPlaceLive gasContext
  supportedStmts supportedTargets supportedExprTraverse supportedStmtTraverse
  allocLimits allocLimitsProps exprLowering vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperAST list

Theorem augassign_entry_rhs_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  `supported_expr tops e` by metis_tac[supported_augassign_contract] >>
  drule supported_expr_main_calls >> simp[EVERY_CONJ] >> strip_tac >>
  drule supported_expr_no_evm_run >> strip_tac >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def]) >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `~is_extcode e` by
    (irule alloc_limits_expr_not_extcode >> qexists_tac `cenv` >>
     fs[stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
  irule stmt_expr_body_pre_alloc >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      alloc_limits_stmt_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem typed_nested_immutable_root_nonword:
  !t vt env id root_ty.
    type_place_target env t = SOME vt /\
    target_root t = TopLevelNameTarget (NONE,id) /\
    t <> TopLevelNameTarget (NONE,id) /\
    FLOOKUP env.bare_global_assignable (NONE,id) = SOME root_ty ==>
    ~is_word_type root_ty
Proof
  ho_match_mp_tac base_assignment_target_induct >>
  simp[target_root_def,type_place_target_SubscriptTarget,type_place_target_AttributeTarget] >>
  rpt strip_tac >>
  Cases_on `t = TopLevelNameTarget (NONE,id)`
  >- (gvs[type_place_target_TopLevelNameTarget] >>
      Cases_on `root_ty` >> gvs[subscript_vtype_def,is_word_type_def])
  >- metis_tac[]
  >- (gvs[type_place_target_TopLevelNameTarget] >>
      Cases_on `root_ty` >> gvs[attribute_type_def,is_word_type_def]) >>
  metis_tac[]
QED

Theorem augassign_entry_target_indices_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) ==>
  target_indices_pre cenv cx env t
Proof
  strip_tac >>
  Cases_on `(?bt fld. t = AttributeTarget bt fld) \/
            (?bt k. t = SubscriptTarget bt k)`
  >- (
    `?pt. supported_target_info tops bindings t = SOME pt` by
      metis_tac[aug_place_supported_stmt_target_info] >>
    drule (cj 1 aug_place_typing) >> strip_tac >>
    `supported_program tops /\ get_module_code cx NONE = SOME tops /\
     (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
    `alloc_limits_target cenv t` by
      fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
    `EVERY (\e. ~is_extcode e) (target_indices t)` by
      metis_tac[alloc_limits_target_indices_not_extcode] >>
    mp_tac (Q.SPECL [`tops`, `bindings`, `t`] supported_target_info_main_calls) >>
    simp[] >> strip_tac >>
    `~supported_target_exists (const_name_root cx) t` by
      (drule_all body_inv_stmt_const_name_free >>
       simp[supported_stmt_expr_exists_def]) >>
    irule aug_place_target_indices_pre >>
    gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        alloc_limits_stmt_def, int_calls_stmt_def] >>
    simp[optionTheory.IS_SOME_EXISTS] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  Cases_on `t` >> gvs[target_indices_pre_def]
QED

Theorem augassign_entry_target_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
  ~immutable_root cx t ==>
  target_pre cenv cx env t es
Proof
  strip_tac >> simp[target_pre_def] >>
  drule_all augassign_entry_target_indices_pre >> simp[]
QED
