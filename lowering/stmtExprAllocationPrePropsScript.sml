Theory stmtExprAllocationPreProps
Ancestors
  allocLimits allocLimitsProps bodyExprPreFacts bodyInvCodeProps bodyInvSplit
  bodyCallSupport bodySim compileUnit exprLowering exprSimHypsDefs finite_map list
  supportedExprTraverse supportedExprs supportedStmtTraverse
  vyperContext vyperTypeCallGraph

Theorem stmt_expr_body_pre_main_alloc_mods:
  contract_inv mods exps ctx cenv cx /\
  supported_expr (main_module mods) e /\
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  ~supported_expr_exists (\e. ~is_extcode e /\ ~byte_widths_expr e) e /\
  alloc_limits_expr cenv e /\
  ~supported_expr_exists (const_name_root_mods mods) e /\
  ~supported_expr_exists (unallocated_bare_global_root cenv env) e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
     occurs_abi_decode_target target (main_module mods)) ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >>
  drule_then assume_tac (cj 1 alloc_limits_expr_exists) >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  mp_tac (Q.INST [`calls` |-> `[]`] stmt_expr_body_pre_main_mods) >>
  fs[DE_MORGAN_THM, LEFT_AND_OVER_OR, supported_expr_exists_disj] >>
  metis_tac[]
QED

Theorem body_inv_stmt_expr_pre_singleton:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  stmt_exprs_ok cenv s /\
  (supported_expr_exists (const_name_root cx) e ==>
   supported_stmt_expr_exists (const_name_root cx) s) /\
  (contract_inv [(NONE,tops)] [] ctx cenv cx /\
   expr_sim_inv_mods [(NONE,tops)] cenv cx env es /\
   ~supported_expr_exists (unallocated_bare_global_root cenv env) e ==>
   expr_body_pre_mods [(NONE,tops)] cenv cx env e es) ==>
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  `~supported_expr_exists (const_name_root cx) e` by
    metis_tac[body_inv_stmt_const_name_free] >>
  drule_all_then assume_tac expr_sim_inv_no_unallocated_bare_globals >>
  `expr_body_pre_mods [(NONE,tops)] cenv cx env e es` by
    fs[expr_sim_inv_split_def] >>
  drule_then assume_tac contract_inv_module_codes >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
  gvs[expr_body_pre_split_def, type_env_all_modules_def, type_env_def,
      FUNION_FEMPTY_2] >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD, source_body_call_supported_def] >>
  rpt strip_tac >> res_tac >> gvs[alistTheory.ALOOKUP_def]
QED
