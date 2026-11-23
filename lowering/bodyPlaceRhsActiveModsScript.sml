Theory bodyPlaceRhsActiveMods
Ancestors
  bodyExprPreFacts bodyInvCodeProps bodyInvMetadataProps bodyInvSplit
  bodySim exprSimHypsDefs allocLimits allocLimitsProps
  bodyAppendStorageFacts stmtSimAugAssignPlace
  supportedStmts supportedStmtTraverse supportedExprTraverse supportedExprs
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness list

(* The expression invariant is supplied at the reached RHS state. Support
   is checked in the active module, and the decoder may occur in any module. *)
Theorem append_active_rhs_pre_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  supported_stmt tops bindings (Append bt e) /\
  type_stmt env ret_ty (Append bt e) = SOME env' /\
  stmt_exprs_ok cenv (Append bt e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Append bt e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (Append bt e) /\
  call_evaluation_safe cx (int_calls_stmt (Append bt e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (Append bt e)) /\
  expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  drule_then strip_assume_tac append_typing_target >>
  `~expr_has_evm_run e` by
    (irule supported_expr_no_evm_run >> qexists_tac `tops` >>
     fs[Once supported_stmt_def, supportedExprsTheory.supported_expr_def]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> fs[int_calls_stmt_def]) >>
  qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
  simp[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, alloc_limits_stmt_def] >>
  strip_tac >> drule_then assume_tac alloc_limits_expr_not_extcode >>
  irule stmt_expr_body_pre_mods >>
  fs[int_calls_stmt_def, EVERY_APPEND, supported_stmt_expr_exists_def, DE_MORGAN_THM] >>
  qexists_tac `[]` >> simp[]
QED

Theorem augassign_active_rhs_pre_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty bt bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty bt bop e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (AugAssign ty bt bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty bt bop e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (AugAssign ty bt bop e)) /\
  expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  drule_then strip_assume_tac aug_place_typing >>
  drule_then (assume_tac o MATCH_MP supported_expr_no_evm_run) supported_augassign_contract >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> fs[int_calls_stmt_def]) >>
  qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
  simp[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, alloc_limits_stmt_def] >>
  strip_tac >> drule_then assume_tac alloc_limits_expr_not_extcode >>
  irule stmt_expr_body_pre_mods >>
  fs[int_calls_stmt_def, EVERY_APPEND, supported_stmt_expr_exists_def, DE_MORGAN_THM] >>
  qexists_tac `[]` >> simp[]
QED
