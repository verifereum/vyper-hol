Theory bodyWriteOperandMods
Ancestors
  bodyExprPreFacts bodyInvCodeProps bodyInvMetadataProps bodyInvSplit
  bodySim exprSimHypsDefs allocLimits allocLimitsProps
  supportedStmts supportedStmtTraverse supportedExprTraverse
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness list

(* The target's call keys precede the RHS keys. Resolution is supplied at
   the statement boundary, in whichever module is active. *)
Theorem assign_rhs_body_pre_linked:
  contract_inv mods exps ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
     (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  EVERY (source_body_call_supported cx)
    (int_calls_stmt (Assign (BaseTarget t) e)) ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `well_typed_expr env e` by
    (qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[type_stmt_def, AllCaseEqs()]) >>
  `~expr_has_evm_run e` by
    (irule supported_expr_no_evm_run >> qexists_tac `tops` >>
     fs[Once supported_stmt_def, supported_assignment_def]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_atarget (BaseTarget t)` >>
     fs[int_calls_stmt_def]) >>
  qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
  simp[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
       alloc_limits_stmt_def] >> strip_tac >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  irule stmt_expr_body_pre_mods >>
  fs[int_calls_stmt_def, EVERY_APPEND, supported_stmt_expr_exists_def,
     DE_MORGAN_THM] >>
  qexists_tac `[]` >> simp[]
QED
