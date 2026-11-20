(* Source-side preconditions for finite-horizon AugAssign composition. *)
Theory augAssignFullEntryPre
Ancestors
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
  drule supported_expr_body_calls >> strip_tac >>
  `~supported_expr_exists (const_name_root cx) e` by
    metis_tac[body_inv_const_name_free] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
     is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule stmt_expr_body_pre_alloc >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      alloc_limits_stmt_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8389 gate widening census (never lands)
Proof
  strip_tac >> simp[target_pre_def] >>
  Cases_on `(?bt fld. t = AttributeTarget bt fld) \/
            (?bt k. t = SubscriptTarget bt k)`
  >- (
    `?pt. supported_target_info tops bindings t = SOME pt` by
      metis_tac[aug_place_supported_stmt_target_info] >>
    drule (cj 1 aug_place_typing) >> strip_tac >>
    `body_stmt_safe tops (AugAssign ty t bop e)` by
      metis_tac[supported_stmt_body_safe] >>
    `supported_program tops /\ get_module_code cx NONE = SOME tops /\
     (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by fs[body_inv_def] >>
    `alloc_limits_target cenv t` by
      fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
    `EVERY (\e. ~is_extcode e) (target_indices t)` by
      metis_tac[alloc_limits_target_indices_not_extcode] >>
    qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
      SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
        int_calls_stmt_def, EVERY_APPEND, DE_MORGAN_THM]) >>
    `~supported_target_exists (const_name_root cx) t` by
      metis_tac[body_inv_target_const_name_free, optionTheory.NOT_SOME_NONE] >>
    `~supported_target_exists call_operands_effect_root t` by
      metis_tac[supported_target_info_storage_syntax, optionTheory.IS_SOME_EXISTS] >>
    irule aug_place_target_indices_pre >>
    gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        alloc_limits_stmt_def, int_calls_stmt_def] >>
    simp[optionTheory.IS_SOME_EXISTS] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  Cases_on `t` >> gvs[target_indices_pre_def]
QED
*)
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
  cheat
QED
