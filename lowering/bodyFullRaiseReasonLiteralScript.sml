(* Literal RaiseReason over one joint finite-horizon execution. *)
Theory bodyFullRaiseReasonLiteral
Ancestors
  bodyFullRaiseReasonLiteralAction

Theorem compile_raise_reason_literal_frag_full:
  !cx ml str DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok cx (Literal (BaseT (StringT ml)) (StringL str)) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Raise (RaiseReason (Literal (BaseT (StringT ml)) (StringL str)))) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
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
  irule compile_raise_reason_literal_frag_full_action >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexistsl_tac [`bindings`,`tops`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`env`,`env'`] >> asm_rewrite_tac[]
QED
