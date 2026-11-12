Theory extRetFrameSplitPtr
Ancestors
  bodyPtrDefs exprLowering

(* A logical partition only: neither branch asserts a stronger producer post. *)
Theorem frame_ret_ok_ptr_layout_split:
  (!cenv' env lctx eo es.
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
      expr_sim_ptr d ctx PG func cenv' cx ty e es /\
      expr_vv_sim_ptr d ctx PG func cenv' cx ty e es) /\
    (eo = NONE \/ ?e. eo = SOME e /\
      lowered_value_type cenv' e = expr_type e) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv'
      (stmt_env cenv' lctx ret_ty (Return eo))
      (eval_stmt cx (Return eo)) es) /\
  (!cenv' env lctx eo es.
    same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
    stmt_exprs_ok cenv' (Return eo) /\
    IS_SOME (type_stmt env ret_ty (Return eo)) /\
    call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
    (!e ty. eo = SOME e ==>
      expr_sim_ptr d ctx PG func cenv' cx ty e es /\
      expr_vv_sim_ptr d ctx PG func cenv' cx ty e es) /\
    (?e. eo = SOME e /\ lowered_value_type cenv' e <> expr_type e) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv'
      (stmt_env cenv' lctx ret_ty (Return eo))
      (eval_stmt cx (Return eo)) es) ==>
  frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty
Proof
  pure_rewrite_tac [frame_ret_ok_ptr_def] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "equal") (mk_asm "unequal")) >>
  rpt strip_tac >> Cases_on `eo`
  >- (asm "equal" irule >> simp[] >> metis_tac[]) >>
  rename1 `SOME e` >>
  Cases_on `lowered_value_type cenv' e = expr_type e`
  >- (asm "equal" irule >> simp[] >> metis_tac[]) >>
  asm "unequal" irule >> simp[] >> metis_tac[]
QED
