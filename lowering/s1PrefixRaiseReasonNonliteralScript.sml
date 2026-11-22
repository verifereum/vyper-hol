(* Request-prefix companion to bodyFullRaiseReasonNonliteral. *)
Theory s1PrefixRaiseReasonNonliteral
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV
  bodyInvCodeProps bodyInvMetadataProps bodyExprPreFacts stateRelProj
  bodyFullShared reasonCompilerProps reasonSourceProps
  gasShadowCompileStmtHelpers gasShadow exprSimHypsDefs bodySim
  supportedStmts supportedStmtTraverse supportedExprTraverse
  stmtSimDefs vyperTypeCallGraph vyperState vyperInterpreter vyperAST

Theorem compile_raise_reason_nonliteral_frag_prefix:
  !cx e DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Raise (RaiseReason e)) /\
  (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason e)) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Raise (RaiseReason e)) = SOME env' /\
  stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
  call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  (!ml str. e <> Literal (BaseT (StringT ml)) (StringL str)) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason e))))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_string_reason tops e` by
    gvs[supported_stmt_raise_reason, supported_raise_reason_def] >>
  drule_then strip_assume_tac supported_string_reason_body_calls >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  drule_all_then strip_assume_tac bodyInvSplitTheory.contract_inv_module_gate >>
  `get_tenv cx = type_env tops` by
    (drule_then assume_tac contract_inv_type_env >>
     fs[vyperContextTheory.type_env_all_modules_def, vyperContextTheory.type_env_def,
        finite_mapTheory.FUNION_FEMPTY_2]) >>
  `~is_extcode e` by
    (irule allocLimitsPropsTheory.alloc_limits_expr_not_extcode >>
     qexists_tac `cenv` >>
     fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
        allocLimitsTheory.alloc_limits_raise_def]) >>
  `~supported_expr_exists (const_name_root cx) e` by
    (drule_all body_inv_stmt_const_name_free >>
     simp[supported_stmt_expr_exists_def, supported_raise_exists_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_raise_reason, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_raise_exists_def, int_calls_stmt_def, int_calls_raise_reason_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    metis_tac[CONJUNCT1 body_expr_prefix_ok_def] >>
  pure_rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule compile_raise_reason_parts >> strip_tac >> gvs[] >>
  drule compile_reason_message_cases >> strip_tac >- metis_tac[] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (mp_tac o REWRITE_RULE [gas_shadow_stmt_def, gas_shadow_raise_reason_def]) >>
  disch_then (mp_then Any strip_assume_tac compile_raise_reason_parts) >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  `gas_shadow_compiles (compile_reason_message cenv e)
     (compile_reason_message (gas_shadow_env T cenv) (gas_shadow_expr e))` by
    irule gas_shadow_compile_reason_message_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[raise_reason_raw_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[loweringPostsTheory.ret_pc_ok_def] >>
  `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
     (vv,sm')` by
    (qpat_assum `compile_reason_message _ (gas_shadow_expr _) _ = _`
       (mp_then Any mp_tac compile_reason_message_cases) >>
     strip_tac
     >- (Cases_on `e` >> gvs[gas_shadow_expr_def] >> metis_tac[]) >>
     gvs[gas_shadow_expr_type]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_expr cx e) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sm'`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp[]) >>
  `!qe. SND (eval_stmt cx (Raise (RaiseReason e)) qe) = SND (eval_expr cx e qe)` by
    (qx_gen_tac `qe` >> rewrite_tac[eval_raise_reason_bind] >>
     once_rewrite_tac[bind_def] >>
     Cases_on `eval_expr cx e qe` >> rename1 `_ = (raw,ee)` >>
     Cases_on `raw` >> simp[] >>
     rename1 `SND (bind (read_result cx tv) _ ee) = ee` >>
     Cases_on `read_result cx tv ee` >> drule_then SUBST_ALL_TAC read_result_state >>
     rename1 `read_result cx tv ee = (res,ee)` >>
     Cases_on `res` >> simp[bind_def] >>
     rename1 `dest_StringV v` >>
     Cases_on `dest_StringV v` >> simp[lift_option_type_def,raise_def,return_def]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED
