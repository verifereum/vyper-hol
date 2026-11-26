(* The linked nonliteral RaiseReason fragment, over the unit execution frame. *)
Theory bodyRaiseReasonNonliteralMods
Ancestors
  bodyFullShadowBodyInv bodyInvCodeProps bodyInvMetadataProps exprBodyPreProps
  stateRelProj bodyFullRaiseReasonContinuation bodyFullPredsMods bodyFullPostsMods
  bodyInvSplit bodyFullShared bodySimFull bodyActiveStmtCallsMods
  bodyReasonReadMods bodyReasonNonliteralEncoderMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  reasonCompilerProps reasonSourceProps gasShadowCompileStmtHelpers
  exprSimSource exprSimHypsDefs exprOperandVar aggregateEvaluatedLayout
  vyperEvalExprPreservesScopesDom gasShadowState gasShadow
  bodyExprPreFacts exprBodyPreTypingProps bodySim supportedStmtTraverse
  supportedExprTraverse supportedStmts vyperTypeSystem vyperTypeCallGraph compileEnv
  exprLoweringProps stmtLowering stmtSimProps stmtSimDefs exprSimDefs bodyPtrDefs
  loweringPosts gasContext vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_raise_reason_nonliteral_frag_full_mods:
  !mods exps cx e DF lo d PG src tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok_mods mods exps cx e /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmt tops bindings (Raise (RaiseReason e)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason e)) ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    body_const_cells_agree_mods mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseReason e)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
      (Raise (RaiseReason e)) /\
    (!key. MEM (vyperSubscriptOverlap$WriteAcc
                  (vyperSubscriptOverlap$StateRef key))
                (vyperSubscriptOverlap$accesses_stmt (Raise (RaiseReason e))) /\
             IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
             IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok_full_mods mods
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (!ml str. e <> Literal (BaseT (StringT ml)) (StringL str)) ==>
    stmt_frag_full_mods
      (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Raise (RaiseReason e))))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_string_reason tops e` by
    gvs[supported_stmt_raise_reason, supported_raise_reason_def] >>
  `well_typed_expr env e` by fs[type_stmt_raise_reason] >>
  `!x. supported_string_reason tops x ==> supported_expr tops x` by
    (gen_tac >> strip_tac >> Cases_on `x` >>
     gvs[supported_string_reason_def, supportedExprsTheory.supported_expr_def,
         supportedExprsTheory.supported_pure_expr_def] >>
     TRY (Cases_on `l` >>
          gvs[supported_string_reason_def, supportedExprsTheory.supported_expr_def,
              supportedExprsTheory.supported_pure_expr_def]) >>
     metis_tac[]) >>
  `supported_expr tops e` by
    metis_tac[] >>
  `~expr_has_evm_run e` by
    drule_then ACCEPT_TAC supported_expr_no_evm_run >>
  `EVERY (source_body_call_supported cx)
      (int_calls_stmt (Raise (RaiseReason e)))` by
    (drule_all_then assume_tac active_stmt_calls_resolve_mods >>
     pop_assum (fn th => assume_tac (CONJUNCT1 th)) >>
     first_x_assum (qspecl_then
       [`bindings`, `Raise (RaiseReason e)`, `ret_ty`, `env'`] mp_tac) >>
     simp[int_calls_stmt_def, int_calls_raise_reason_def]) >>
  `alloc_limits_expr cenv e` by
    fs[stmt_exprs_ok_flat, allocLimitsTheory.alloc_limits_stmt_def,
       allocLimitsTheory.alloc_limits_raise_def] >>
  `~is_extcode e` by
    metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
  `~supported_expr_exists (const_name_root_mods cenv.ce_modules) e` by
    (qpat_x_assum `stmt_exprs_ok cenv _` mp_tac >>
     simp[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
          supported_raise_exists_def]) >>
  `cenv.ce_modules = mods` by
    drule_then ACCEPT_TAC contract_inv_cenv_modules >>
  `~supported_expr_exists (const_name_root_mods mods) e` by
    gvs[] >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre_mods)) >>
     gvs[type_stmt_raise_reason, stmt_exprs_ok_flat,
         supported_stmt_expr_exists_def, supported_raise_exists_def,
         int_calls_stmt_def, int_calls_raise_reason_def] >>
     rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     TRY (drule_then assume_tac contract_inv_type_env >> simp[])) >>
  `expr_vv_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
      (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     metis_tac[]) >>
  pure_rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
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
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  suspend "expression"
QED

Resume compile_raise_reason_nonliteral_frag_full_mods[expression]:
  `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
     (vv,sm')` by
    (qpat_assum `compile_reason_message _ (gas_shadow_expr _) _ = _`
       (mp_then Any mp_tac compile_reason_message_cases) >>
     strip_tac
     >- (Cases_on `e` >> gvs[gas_shadow_expr_def] >> metis_tac[]) >>
     gvs[gas_shadow_expr_type]) >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_mods_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sm'`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "compose"
QED

Resume compile_raise_reason_nonliteral_frag_full_mods[compose]:
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ reasonQ reasonR` >>
  pure_rewrite_tac[eval_raise_reason_bind] >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts,storage_trace_frame_raise]) >>
  qexists_tac `\H res ee G tn t. reasonQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`] >- suspend "normal" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `reasonR`] >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  `expr_exit (INR y : unit + exception) r` by
    (qpat_assum `expr_exit _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[expr_exit_INR_type]) >>
  `!ir t. r <> IntRet ir t` by
    (qpat_assum `expr_exit _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `expr_exit _ _` mp_tac >>
     Cases_on `y` >> simp[expr_exit_def] >>
     rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  fs[stmt_exit_ptr_def, halt_exit_def]
QED

Resume compile_raise_reason_nonliteral_frag_full_mods[normal]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `reasonQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qexists_tac `tv` >> conj_tac >- simp[] >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `?str. read_result cx tv mid = (INL (StringV str),mid) /\
    !tail. bind (read_result cx tv)
      (\v. bind (lift_option_type (dest_StringV v) "not StringV")
        (\str. raise (AssertException str))) (mid with gas_obs := tail) =
      (INR (AssertException str) : unit + exception,mid with gas_obs := tail)` by
    (mp_tac (Q.GENL [`r`,`H`]
      (Q.INST [`ee` |-> `mid`]
       (INST_TYPE [alpha |-> ``:256``]
        bodyReasonReadModsTheory.raise_reason_raw_string_mods))) >>
     simp[] >> disch_then irule >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`e`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `well_typed_expr env e` by metis_tac[expr_body_pre_static_facts] >>
  drule_all reasonSourcePropsTheory.supported_reason_string_type >>
  disch_then (qx_choose_then `cap` assume_tac) >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
  fs[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_body_pre_mods cenv.ce_modules cenv cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    (`expr_body_pre_mods cenv.ce_modules cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) <=>
       expr_body_pre_mods cenv.ce_modules cenv cx env e es` by
       gvs[expr_body_pre_mods_def, expr_sim_inv_mods_def,
           vyperTypeInvariantsTheory.gas_obs_type_invariants] >>
     metis_tac[vyperTypeInvariantsTheory.gas_obs_type_invariants]) >>
  drule_all expr_body_pre_mods_runtime_typing >> strip_tac >>
  qpat_assum `compile_expr _ _ e sa = _`
    (mp_then Any strip_assume_tac (cj 1 compile_expr_grows)) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all reason_encoder_size_mods >> strip_tac >>
  `get_tenv cx = env.type_defs` by
    metis_tac[vyperTypeExtCallCoreTheory.runtime_consistent_get_tenv] >>
  `(do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL (StringV str),mid)` by simp[bind_def] >>
  `?rty. evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
      value_has_type rty (StringV str)` by
    (drule_all bodySimStmtFactsTheory.expr_body_pre_eval_mods >>
     fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr _ _ e sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[]) >>
  fs[] >>
  `?z Gf tnf. !H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (Abort Revert_abort z,Gf,tnf)` by
    (irule (INST_TYPE [alpha |-> ``:type``] reason_nonliteral_encoder_origin_ptr_mods) >>
     simp[] >>
     qpat_assum `compile_expr _ _ e sa = _` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >>
     simp[] >>
     rpt (goal_assum (drule_at Any)) >>
     simp[] >>
     qexists_tac `rty` >>
     gvs[arithmeticTheory.ADD_COMM]) >>
  irule gas_outcome_full_mods_exit_revert >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gf`,`mid`,`INR (AssertException str)`,`tnf`,`z`] >>
  simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def, expr_exit_def,
       halt_exit_def]
QED

Finalise compile_raise_reason_nonliteral_frag_full_mods
