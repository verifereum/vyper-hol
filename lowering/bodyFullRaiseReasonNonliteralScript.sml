(* Nonliteral RaiseReason over the joint finite-horizon judgment. *)
Theory bodyFullRaiseReasonNonliteral
Ancestors
  bodyFullRaiseReasonContinuation bodyFullPreds bodySimFull bodyFullShared bodyInvNoDalloca
  reasonCompilerProps reasonSourceProps gasShadowCompileStmtHelpers
  reasonResourcesPtr reasonRaiseContinuationPtr stmtReasonKindsMemory
  exprSimSource exprSimHypsDefs exprOperandVar aggregateEvaluatedLayout vyperEvalExprPreservesScopesDom
  gasOutcomeFullCompose gasOutcomeFull gasShadowState gasShadow
  bodyExprPreFacts bodySim supportedStmtTraverse supportedExprTraverse
  supportedStmts vyperTypeSystem exprSimHyps allocLimitsProps
  vyperTypeCallGraph compileEnv exprLoweringProps stmtLowering
  loweringPosts gasContext gasExemptCert vyperStorageTrace vyperStorageFootprint
  exprSimDefs stmtSimDefs stmtSimProps bodyPtrDefs
  vyperInterpreter vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_raise_reason_nonliteral_frag_full:
  !cx e DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (Raise (RaiseReason e)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason e)) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseReason e)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseReason e)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e))) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (!ml str. e <> Literal (BaseT (StringT ml)) (StringL str)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason e))))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_string_reason tops e` by
    gvs[supported_stmt_def, supported_raise_reason_def] >>
  drule_then strip_assume_tac supported_string_reason_body_calls >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> gvs[body_inv_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_raise_exists_def, int_calls_stmt_def,
         int_calls_raise_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    metis_tac[body_expr_full_ok_def] >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  drule compile_raise_reason_parts >> strip_tac >> gvs[] >>
  suspend "layout"
QED

Resume compile_raise_reason_nonliteral_frag_full[layout]:
  drule compile_reason_message_cases >> strip_tac >- metis_tac[] >>
  `stmt_env cenv lctx ret_ty (Raise (RaiseReason (gas_shadow_expr e))) shadow_sa =
     (cenv,shadow_sb)` by gvs[gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  qpat_assum `stmt_env _ _ _ _ shadow_sa = _`
    (mp_then Any strip_assume_tac compile_raise_reason_parts) >>
  `vv' = vv /\ gas_shadow_state sm sm'` by
    (mp_tac gas_shadow_compile_reason_message >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[raise_reason_raw_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  suspend "expression"
QED

Resume compile_raise_reason_nonliteral_frag_full[expression]:
  `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,sm')` by
    (qpat_assum `compile_reason_message _ (gas_shadow_expr _) _ = _`
       (mp_then Any mp_tac compile_reason_message_cases) >>
     strip_tac
     >- (Cases_on `e` >> gvs[gas_shadow_expr_def] >> metis_tac[]) >>
     gvs[gas_shadow_expr_type]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sm'`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "compose"
QED

Resume compile_raise_reason_nonliteral_frag_full[compose]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ reasonQ reasonR` >>
  pure_rewrite_tac[eval_raise_reason_bind] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
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
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `reasonR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  simp[stmt_exit_ptr_def] >>
  qpat_x_assum `expr_exit _ _` mp_tac >>
  qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[halt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_raise_reason_nonliteral_frag_full[normal]:
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
    (mp_tac (Q.GENL [`r`,`H`] (Q.INST [`ee` |-> `mid`] (INST_TYPE [alpha |-> ``:256``] raise_reason_raw_string))) >>
     simp[] >> disch_then irule >>
     qexistsl_tac [`storage_trace_horizon mid.storage_trace`,`e`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule_all supported_reason_string_type >>
  disch_then (qx_choose_then `cap` assume_tac) >>
  `post_value_type cenv e = expr_type e` by
    simp[post_value_type_bytestring, is_bytestring_type_def] >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
  fs[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  qpat_assum `compile_expr _ _ e sa = _`
    (mp_then Any strip_assume_tac (cj 1 compile_expr_grows)) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     ~is_word_type (post_value_type cenv e) ==>
     type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
     type_memory_size rt < 2**64` by metis_tac[body_post_type_allocation_bound] >>
  `type_alloc_ok cenv (BaseT (StringT cap))` by
    metis_tac[expr_body_pre_def, alloc_limits_expr_type_alloc_ok] >>
  `64 + type_memory_bytes cenv (BaseT (StringT cap)) < dimword(:256)` by
    metis_tac[reason_encoder_allocation_limit] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr _ _ e sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[]) >>
  fs[] >>
  `?z Gf tnf. !H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G1,tn1) [] (Abort Revert_abort z,Gf,tnf)` by
    (irule (INST_TYPE [alpha |-> ``:type``] reason_nonliteral_encoder_origin_ptr) >>
     simp[] >>
     qpat_assum `compile_expr _ _ e sa = _` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >>
     rpt (goal_assum (drule_at Any)) >>
     simp[] >>
     qexists_tac `tvt` >> gvs[]) >>
  irule gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gf`,`mid`,`Abort Revert_abort z`,
                           `INR (AssertException str)`,`tnf`] >>
               simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def, expr_exit_def]) >>
  simp[fragExecTheory.exit_result_def, stmt_exit_ptr_def, expr_exit_def]
QED

Finalise compile_raise_reason_nonliteral_frag_full
