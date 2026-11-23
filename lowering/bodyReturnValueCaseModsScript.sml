Theory bodyReturnValueCaseMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyExprPreFacts bodyInvCodeProps
  bodyInvMetadataProps bodySim supportedStmts supportedStmtTraverse
  supportedExprTraverse allocLimits allocLimitsProps vyperTypeSystem
  vyperTypeCallGraph gasShadow

(* Resolve the operand's call keys in the statement's active module. *)
Theorem body_return_case_full_mods:
  !mods exps cx e.
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\
       body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
    body_expr_full_ok_mods mods exps cx e ==>
    body_stmt_full_ok_mods mods exps cx (Return (SOME e))
Proof
  rpt gen_tac >> disch_then (mk_asm "resolve") >> disch_tac >>
  rw[body_stmt_full_ok_mods_def] >>
  `EVERY (source_body_call_supported cx) (int_calls_stmt (Return (SOME e)))` by
    (asm "resolve" irule >> metis_tac[]) >>
  `supported_expr tops e` by fs[Once supported_stmt_def] >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre_mods)) >>
     fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        supported_expr_exists_def, type_stmt_def, int_calls_stmt_def,
        int_calls_expr_def, alloc_limits_stmt_def, alloc_limits_expr_def] >>
     metis_tac[alloc_limits_expr_not_extcode]) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_x_assum `frame_ret_ok_full_mods _ _ _ _ _ _`
    (qspecl_then [`cenv`, `env`, `lctx`, `SOME e`, `es`] mp_tac o
     REWRITE_RULE [frame_ret_ok_full_mods_def]) >>
  simp[same_frame_refl, gas_shadow_stmt_def] >>
  disch_then irule >> gen_tac >>
  first_assum irule >> metis_tac[]
QED
