(*
 * Assert with a reason in the full body induction (bodySimFullMain), over
 * the finite-horizon joint judgment: the condition's joint fragment and
 * its JNZ (bodyFullExits' compile_assert_cond_path shape), then on the
 * false branch the reason's joint fragment and the REVERT, sharing one
 * origin/memory/pointer witness.
 *
 * TOP-LEVEL:
 *   compile_assert_reason_frag_full -- body_assert_reason_case_full's fragment
 *)
Theory bodyFullAssertReason
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

Theorem compile_assert_reason_frag_full:
  !cx e se DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (Assert e (AssertReason se)) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assert e (AssertReason se)) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assert e (AssertReason se)) = SOME env' /\
    stmt_exprs_ok cenv (Assert e (AssertReason se)) /\
    call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason se))) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assert e (AssertReason se)))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assert e (AssertReason se))))
      (eval_stmt cx (Assert e (AssertReason se))) es
Proof
  cheat
QED
