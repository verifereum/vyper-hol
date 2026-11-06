Theory bodyPtrBopPairOutcome
Ancestors
  bodyPtrBopOperands bodyPtrBopOperandRetention gasSummaryComposePtr
  stmtSimLogArgs exprSimOperators

(* Keep the first operand at the second operand's exit.  Only its value
   footprint is retained; this deliberately asserts no buffer coverage. *)
Theorem bop_pair_first_post_kept:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sb.cs_next_id <= sc.cs_next_id /\ wb_frame cenv es sb s t /\
  (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l) /\
  log_arg_rel cenv cx sa sb es s (op,ty) v /\
  ptr_val_ok cx ty v op G tn s /\
  ghost_kept cenv es sb G tn s G' tn' /\
  eval_operand op t = eval_operand op s /\
  (~is_word_type ty ==> evaluate_type (get_tenv cx) ty = SOME tv) ==>
  log_arg_rel cenv cx sa sc es' t (op,ty) v /\
  ptr_val_ok cx ty v op G' tn' t
Proof
  strip_tac >> conj_tac
  >- (irule log_arg_rel_frame >> simp[] >> metis_tac[]) >>
  irule bop_argument_ptr_val_kept >>
  fs[log_arg_rel_def] >> metis_tac[]
QED

Theorem bop_pair_operand_judgments:
  body_exprs_ptr_ok cx [e1;e2] /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  eval_expr cx e1 s = (INL tv,t) /\
  read_result cx tv s1 = (INL v,t1) /\
  expr_sim_inv cenv cx env es' ==>
  expr_sim_ptr d ctx PG func cenv cx ty1 e1 es /\
  expr_vv_sim_ptr d ctx PG func cenv cx ty1 e1 es /\
  expr_sim_ptr d ctx PG func cenv cx ty2 e2 es' /\
  expr_vv_sim_ptr d ctx PG func cenv cx ty2 e2 es'
Proof
  strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  fs[body_exprs_ptr_ok_pair, bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
  metis_tac[]
QED
