(* Operand preconditions use the caller's active module, not the error owner. *)
Theory bodyCustomErrorArgPreMods
Ancestors
  bodyFullPredsMods bodyExprPreFacts bodyInvCodeProps bodyInvMetadataProps
  supportedStmts supportedExprs supportedStmtTraverse supportedExprTraverse
  allocLimits allocLimitsProps exprSimSource constSubstCorrect
  vyperTypeSystem vyperTypeCallGraph list

Theorem custom_error_arg_pre_mods:
  (!ctx cenv src tops env es bindings s ret_ty env'.
     contract_inv mods exps ctx cenv cx /\
     module_body_inv mods src tops cenv cx /\
     expr_sim_inv_mods mods cenv cx env es /\
     body_const_cells_agree_mods mods cx env es /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
     EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  supported_stmt tops bindings (Raise (RaiseCustomError err)) /\
  type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
  stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
     (Raise (RaiseCustomError err)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Raise (RaiseCustomError err)) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
  args = custom_error_exprs err ==>
  !e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st /\
    body_const_cells_agree_mods mods cx env st ==>
    expr_body_pre_mods mods cenv cx env e st
Proof
  disch_then (mk_asm "resolve") >> strip_tac >> rpt gen_tac >> strip_tac >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Raise (RaiseCustomError err)))` by
    (asm "resolve" irule >> metis_tac[]) >>
  asm_x "resolve" kall_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `supported_expr tops e` by
    (fs[Once supported_stmt_def, supported_raise_reason_def, supported_expr_def] >>
     metis_tac[EVERY_MEM]) >>
  drule_then assume_tac supported_expr_no_evm_run >>
  `well_typed_expr env e` by
    (fs[type_stmt_def, AllCaseEqs(), well_typed_custom_error_def,
        frame_well_typed_exprs_every] >> metis_tac[EVERY_MEM]) >>
  `alloc_limits_expr cenv e` by
    (fs[stmt_exprs_ok_flat, alloc_limits_stmt_def, alloc_limits_raise_def] >>
     metis_tac[alloc_limits_exprs_mem]) >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  `!P. supported_expr_exists P e ==>
       supported_stmt_expr_exists P (Raise (RaiseCustomError err))` by
    (simp[supported_stmt_expr_exists_def, supported_raise_exists_def, EXISTS_MEM] >>
     metis_tac[]) >>
  irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre_mods)) >>
  fs[stmt_exprs_ok_flat, int_calls_stmt_def, int_calls_raise_reason_def] >>
  metis_tac[call_evaluation_safe_exprs_mem, int_calls_exprs_every_mem]
QED
