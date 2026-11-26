(* Condition entry for an assertion in any active module of a linked unit. *)
Theory bodyAssertConditionPreMods
Ancestors
  bodyFullPredsMods bodyExprPreFacts bodyInvCodeProps bodyInvMetadataProps
  supportedStmts supportedExprs supportedStmtTraverse supportedExprTraverse
  allocLimits allocLimitsProps vyperTypeSystem vyperTypeCallGraph

Theorem assert_condition_pre_active_mods:
  (!ctx cenv src tops env es bindings s ret_ty env'.
     contract_inv mods exps ctx cenv cx /\
     module_body_inv mods src tops cenv cx /\
     expr_sim_inv_mods mods cenv cx env es /\
     body_const_cells_agree_mods mods cx env es /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  supported_stmt tops bindings (Assert e reason) /\
  type_stmt env ret_ty (Assert e reason) = SOME env' /\
  stmt_exprs_ok cenv (Assert e reason) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) (Assert e reason) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (Assert e reason) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (Assert e reason)) ==>
  expr_type e = BaseT BoolT /\ expr_body_pre_mods mods cenv cx env e es
Proof
  disch_then (mk_asm "resolve") >> strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Assert e reason))` by
    (asm "resolve" irule >> metis_tac[]) >>
  asm_x "resolve" kall_tac >>
  `well_typed_expr env e /\ expr_type e = BaseT BoolT` by
    (Cases_on `reason` >> gvs[type_stmt_def, AllCaseEqs()]) >>
  `supported_expr tops e` by
    fs[Once supported_stmt_def, supported_expr_def] >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `alloc_limits_expr cenv e` by fs[stmt_exprs_ok_flat, alloc_limits_stmt_def] >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  simp[] >>
  irule (Q.INST [`calls` |-> `int_calls_assert_reason reason`]
    (SPEC_ALL stmt_expr_body_pre_mods)) >>
  fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `reason` >> simp[]
QED
