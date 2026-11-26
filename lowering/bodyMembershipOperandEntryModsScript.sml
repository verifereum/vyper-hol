(* Source preconditions at the two reached operands of ordinary membership. *)
Theory bodyMembershipOperandEntryMods
Ancestors
  bodyFullPredsMods bodyBopBytestringBindMods exprBodyPreProps exprSimSource
  exprSimHypsDefs supportedExprTraverse allocLimits constSubstCorrect
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperAST vyperState stmtSimDefs vyperStorageTrace list
Libs monadsyntax

Theorem membership_bop_arg_pre[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) args) es /\
  MEM e args /\ expr_sim_inv_mods mods cenv cx env mid ==>
  expr_body_pre_mods mods cenv cx env e mid
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, EXISTS_MEM] >>
  strip_tac >>
  `!p. supported_expr_exists p e ==>
       supported_expr_exists p (Builtin ann (Bop bop) args)` by
    (simp[Once supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  `alloc_limits_expr cenv e` by
    (irule alloc_limits_builtin_arg >>
     qexistsl_tac [`ann`,`args`,`Bop bop`] >> simp[]) >>
  simp[] >> rpt conj_tac >> metis_tac[]
QED

Theorem membership_operand_entry_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  body_exprs_full_ok_mods mods exps cx [e1;e2] ==>
  body_expr_full_ok_mods mods exps cx e1 /\
  expr_body_pre_mods mods cenv cx env e1 es /\
  (!obs needle mid.
     mid.gas_obs = [] /\
     (!tail. bind (eval_expr cx e1) (read_result cx)
        (es with gas_obs := obs ++ tail) = (INL needle,mid with gas_obs := tail)) ==>
     body_expr_full_ok_mods mods exps cx e2 /\
     expr_body_pre_mods mods cenv cx env e2 mid /\
     body_const_cells_agree_mods mods cx env mid /\
     value_runtime_typed env (expr_type e1) needle /\
     MAP FDOM es.scopes = MAP FDOM mid.scopes /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `expr_body_pre_mods mods cenv cx env e1 es` by
    (irule membership_bop_arg_pre >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ [e1;e2]` mp_tac >>
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all_then (strip_assume_tac o Q.SPEC `st0`) bop_bytestring_operand_source_mods >>
  drule_then (assume_tac o SRULE []) eval_read_preserves_scopes_dom >>
  simp[] >> conj_tac
  >- (drule_then strip_assume_tac (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >>
      `body_exprs_full_ok_mods mods exps cx [e2]` by
        (first_x_assum irule >> rpt (goal_assum (drule_at Any))) >>
      fs[Once body_exprs_full_ok_mods_def]) >>
  irule membership_bop_arg_pre >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]
QED
