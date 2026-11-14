(*
 * The log statement of the full body induction (bodySimFullMain), over the
 * finite-horizon joint judgment: the arguments' joint fragments, the
 * event's memory encoding and the LOG instruction share one origin/
 * memory/pointer witness.
 *
 * TOP-LEVEL: body_log_case_full's two leaves, split on whether the
 * event declares only scalar field types:
 *   compile_log_frag_full -- the scalar arm
 *   body_log_aggregate_full -- the aggregate arm
 *)
Theory bodyFullLog
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

(* Admitted: the event declares only scalar field types. *)
Theorem compile_log_frag_full:
  !cx id args fields DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx args /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (Log id args) /\
    supported_event_fields tops id = SOME fields /\
    EVERY supported_scalar_type (MAP (SND o FST) fields) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id args)))
      (eval_stmt cx (Log id args)) es
Proof
  cheat
QED

(* Admitted: Log whose event declares an aggregate field. *)
Theorem body_log_aggregate_full:
  !cx id args fields DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx args /\
    body_inv tops ctx cenv cx /\
    supported_log tops id args /\
    supported_event_fields tops id = SOME fields /\
    ~EVERY supported_scalar_type (MAP (SND o FST) fields) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id args) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Log id args) = SOME env' /\
    stmt_exprs_ok cenv (Log id args) /\
    call_evaluation_safe cx (int_calls_stmt (Log id args)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id args))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id args)))
      (eval_stmt cx (Log id args)) es
Proof
  cheat
QED
