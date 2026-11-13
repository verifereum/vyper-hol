(*
 * Per-clause leaves of bodyFullCases' statement cases, at the joint
 * judgments of bodySimFull.  Each case in bodyFullCases unfolds
 * body_stmt_full_ok and supported_stmt and hands every supported_stmt
 * clause to its leaf here, whose premises are that clause's classifier and
 * the case's IHs, so widening one clause touches only its leaf.  Append's
 * leaves split by target shape and keep the body_stmt_full_ok form.
 *
 * TOP-LEVEL: the body_*_full leaves below.
 *)
Theory bodyFullCaseLeaves
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

(* Admitted: AnnAssign, under its supported_stmt clause. *)
Theorem body_annassign_full:
  !cx id typ e DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_place_type tops typ /\
    (supported_copy_types typ (expr_type e) \/ arg_type_fits (expr_type e) typ) /\
    supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* Admitted: Assert with a string reason, under its supported_stmt clause. *)
Theorem body_assert_reason_full:
  !cx e se DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_pure_expr tops e /\ supported_string_reason tops se /\
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

(* Admitted: assignment to a base target, under its supported_stmt clause. *)
Theorem body_assign_base_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t'.
       eval_expr cx e s'' = (INL pv,t') ==> body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_assignment tops bindings (BaseTarget t) e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED

(* Admitted: assignment to a tuple target, under its supported_stmt clause. *)
Theorem body_assign_tuple_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_assignment tops bindings (TupleTarget gs) e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* Admitted: augmented assignment, under its supported_stmt clause. *)
Theorem body_augassign_full:
  !cx ty t bop e DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t /\
    body_inv tops ctx cenv cx /\
    (supported_target tops bindings t \/ supported_aug_target tops bindings t) /\
    supported_expr tops e /\
    supported_binop bop ty (expr_type e) F (supported_nonnegative_literal e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign ty t bop e)))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  cheat
QED

(* Admitted: a for loop, under its supported_stmt clause; the loop body's
   supported_stmts conjunct is what the body IH body_for_full_ok consumes. *)
Theorem body_for_full:
  !cx id typ it n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) /\
    body_inv tops ctx cenv cx /\
    supported_type_namespace typ /\ supported_iterator tops typ it n /\
    supported_stmts tops bindings body /\
    ~supported_stmts_expr_exists expr_internal_call_root body /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ it n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ it n body) = SOME env' /\
    stmt_exprs_ok cenv (For id typ it n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ it n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ it n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ it n body)))
      (eval_stmt cx (For id typ it n body)) es
Proof
  cheat
QED

(* Admitted: Log whose argument types equal the event's field types. *)
Theorem body_log_exact_full:
  !cx id es DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx es /\
    body_inv tops ctx cenv cx /\
    supported_log tops id es /\ supported_log_exact tops id es /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id es) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Log id es) = SOME env' /\
    stmt_exprs_ok cenv (Log id es) /\
    call_evaluation_safe cx (int_calls_stmt (Log id es)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id es))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id es)))
      (eval_stmt cx (Log id es)) es
Proof
  cheat
QED

(* Admitted: Log with an argument widened to its event field's type. *)
Theorem body_log_widened_full:
  !cx id es DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_exprs_full_ok cx es /\
    body_inv tops ctx cenv cx /\
    supported_log tops id es /\ ~supported_log_exact tops id es /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Log id es) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Log id es) = SOME env' /\
    stmt_exprs_ok cenv (Log id es) /\
    call_evaluation_safe cx (int_calls_stmt (Log id es)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Log id es))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Log id es)))
      (eval_stmt cx (Log id es)) es
Proof
  cheat
QED

(* Admitted: Raise with a string reason, under its supported_stmt clause. *)
Theorem body_raise_reason_full:
  !cx e DF lo d PG tops ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_string_reason tops e /\
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

(* Admitted: the top-level storage/transient dynamic array. *)
Theorem body_append_storage_full:
  !cx nid e.
    (!s'' p t'.
       eval_target_place cx (TopLevelNameTarget nid) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (TopLevelNameTarget nid) e)
Proof
  cheat
QED

(* A local memory dynamic array named directly: vacuous until
   supported_append_target admits NameTarget. *)
Theorem body_append_local_full:
  !cx id e.
    (!s'' p t'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  rw[body_stmt_full_ok_def, supported_stmt_def, supported_append_target_def]
QED

(* A dynamic array reached through subscripts/attributes: vacuous until
   supported_append_target admits those targets. *)
Theorem body_append_nested_full:
  !cx t e.
    (!id. t <> NameTarget id) /\ (!nid. t <> TopLevelNameTarget nid) /\
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (Append t e)
Proof
  rw[body_stmt_full_ok_def] >> Cases_on `t` >>
  gvs[supported_stmt_def, supported_append_target_def]
QED
