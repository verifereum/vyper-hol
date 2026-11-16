(* Literal RaiseReason over one joint finite-horizon execution. *)
Theory bodyFullRaiseReasonLiteral
Ancestors
  bodyFullRaiseReasonLiteralEntry bodyFullRaiseReasonLiteralEncoder
  bodyFullPreds bodySimFull bodyFullShared bodyInvNoDalloca reasonCompilerProps reasonSourceProps
  reasonResourcesPtr reasonTypingProps gasOutcomeFullCompose gasOutcomeFull
  bodyExprPreFacts exprSimHypsDefs bodySim supportedStmtTraverse supportedExprTraverse
  supportedStmts vyperTypeSystem exprSimHyps allocLimitsProps
  vyperTypeCallGraph compileEnv exprLoweringProps stmtLowering
  loweringPosts gasContext gasShadowState gasShadow bodyPtrDefs exprSimDefs stmtSimDefs stmtSimProps
  vyperStorageTrace vyperStorageFootprint fragGasOriginPtrLoop fragExec
  vyperInterpreter vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_raise_reason_literal_frag_full:
  !cx ml str DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok cx (Literal (BaseT (StringT ml)) (StringL str)) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))))
      (eval_stmt cx (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str))))) es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_string_reason tops (Literal (BaseT (StringT ml)) (StringL str))` by
    gvs[supported_stmt_def, supported_raise_reason_def] >>
  drule_then strip_assume_tac supported_string_reason_body_calls >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> gvs[body_inv_def]) >>
  `expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_raise_exists_def, int_calls_stmt_def,
         int_calls_raise_reason_def, body_inv_def] >>
     conj_tac
     >- simp[supported_expr_exists_def, const_name_root_def] >>
     qexists_tac `[]` >> simp[]) >>
  `type_alloc_ok cenv (BaseT (StringT ml))` by
    metis_tac[expr_body_pre_def, alloc_limits_expr_type_alloc_ok, expr_type_def] >>
  `64 + type_memory_bytes cenv (BaseT (StringT ml)) < dimword(:256)` by
    metis_tac[reason_encoder_allocation_limit] >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  drule compile_raise_reason_parts >> strip_tac >> gvs[] >>
  drule compile_reason_message_cases >> strip_tac >> gvs[] >>
  drule_all raise_reason_compiler_code >> strip_tac >>
  suspend "entry"
QED

Resume compile_raise_reason_literal_frag_full[entry]:
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "domain" >>
  irule gas_outcome_full_bad_nil >> simp[eval_raise_string_literal_reason]
QED

Resume compile_raise_reason_literal_frag_full[domain]:
  drule literal_reason_source_resources >> strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  drule_all reason_literal_message_full_entry >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    strip_assume_tac) >>
  suspend "encoder"
QED

Resume compile_raise_reason_literal_frag_full[encoder]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qspecl_then [`MAP (n2w o ORD) str`,`ml`,`sa`] mp_tac
       ci_mono_compile_bytelike_literal >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `?z Gz tz. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,Gf,tnf) [] (Abort Revert_abort z,Gz,tz)` by
    (irule reason_literal_encoder_origin_ptr >>
     simp[expr_type_def] >>
     qpat_assum `compile_bytelike_literal _ _ _ = _` (irule_at Any) >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexists_tac `d` >> conj_tac
     >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     qpat_x_assum `compile_revert_with_reason _ _ _ _ _ = _` mp_tac >>
     simp[expr_type_def]) >>
  suspend "exit"
QED

Resume compile_raise_reason_literal_frag_full[exit]:
  irule gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gz`,`es`,`Abort Revert_abort z`,
                            `INR (AssertException str)`,`tz`] >>
    simp[eval_raise_string_literal_reason, exit_result_def,
         stmt_exit_ptr_def, expr_exit_def, halt_exit_def] >>
    rpt strip_tac >>
    irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gf`,`t`,`tnf`] >>
    conj_tac >> first_x_assum drule >> simp[]) >>
  simp[exit_result_def, stmt_exit_ptr_def, expr_exit_def, halt_exit_def]
QED

Finalise compile_raise_reason_literal_frag_full
