(*
 * Raise with a reason in the full body induction (bodySimFullMain), over
 * the finite-horizon joint judgment: the reason's joint fragment, its
 * revert-data encoding and the REVERT share one origin/memory/pointer
 * witness.
 *
 * TOP-LEVEL:
 *   compile_raise_reason_frag_full -- body_raise_reason_case_full's fragment
 *)
Theory bodyFullRaiseReason
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_raise_reason_frag_full:
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
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseReason e)))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Raise (RaiseReason e))))
      (eval_stmt cx (Raise (RaiseReason e))) es
Proof
  cheat
QED
