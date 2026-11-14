(*
 * Annotated declaration over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAnnAssign
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  bodyFullAnnAssignMemoryPost
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

(* A word local. *)
Theorem body_annassign_word_full:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    is_word_type typ ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* A memory local whose source is stored at its own layout. *)
Theorem body_annassign_memory_full:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~is_word_type typ /\
    0 < type_memory_bytes cenv typ /\
    (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* A memory local whose source is a widened aggregate. *)
Theorem body_annassign_widened_full:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~is_word_type typ /\
    0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* Any other declared type. *)
Theorem body_annassign_other_full:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~is_word_type typ /\
    ~(expr_type e = typ \/ is_bytestring_type typ \/
      has_length_word typ /\ is_empty_value_expr e) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED
