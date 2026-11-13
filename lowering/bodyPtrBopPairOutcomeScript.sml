Theory bodyPtrBopPairOutcome
Ancestors
  bodyPtrBopOperands bodyPtrBopOperandRetention gasSummaryComposePtr
  stmtSimLogArgs exprSimOperators typedWordArgsFactsPtr

(* Keep the first operand at the second operand's exit.  Only its value
   footprint is retained; this deliberately asserts no buffer coverage. *)
Theorem bop_pair_first_post_kept:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sb.cs_next_id <= sc.cs_next_id /\ wb_frame cenv es ee sb s t /\
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

(* One operand followed by a continuation.  The two certificate premises are
   deliberately explicit: an exempt child is not an ordinary pointer path. *)
Theorem bop_operand_outcome_ptr:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs rr ee.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (rr,ee)
    ==> P rr ee) /\
  (!v ee G tn t.
    expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    P (INL v) ee /\ ee.gas_obs = [] /\ ~t.vs_halted ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next v) (ee,t,G,tn) Q (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (next v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  irule gas_outcome_ptr_bind >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >>
  qexistsl_tac
    [`\res ee G tn t. (?v. res = INL v /\
       expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv cx ee G tn t /\
       ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
       ghost_kept cenv es sa G0 tn0 s0 G tn) /\
       P res ee /\ ee.gas_obs = [] /\ ~t.vs_halted`,
     `\res ee gt r. expr_exit res r`] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- (Cases_on `r` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
      fs[] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  ho_match_mp_tac gas_outcome_ptr_source_facts >>
  conj_tac
  >- (fs[bodyPtrDefsTheory.expr_sim_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* The normal pair boundary: first operand representation and the entry ghost
   frame survive the second evaluation.  The second operand keeps its own
   expr_post and buffer certificate, supplied separately by the caller. *)
Theorem bop_pair_posts_kept:
  expr_post ctx func cenv cx e1 es sa sb s0 es1 v1 x s1 /\
  expr_post ctx func cenv cx e2 es1 sb sc s1 es2 v2 y s2 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_id <= sc.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sb z) /\ (!l. x <> Label l) /\
  log_arg_clear cenv cx (post_value_type cenv e1) v1 /\
  ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 s1 /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 /\
  eval_operand x s2 = eval_operand x s1 /\
  (~is_word_type (post_value_type cenv e1) ==>
    evaluate_type (get_tenv cx) (post_value_type cenv e1) = SOME tv) /\
  stmt_state_rel ctx func cenv cx es s0 ==>
  log_arg_rel cenv cx sa sc es2 s2 (x,post_value_type cenv e1) v1 /\
  ptr_val_ok cx (post_value_type cenv e1) v1 x G2 tn2 s2 /\
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `wb_frame cenv es es1 sa s0 s1` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame cenv es1 es2 sb s1 s2` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `stmt_state_rel ctx func cenv cx es1 s1` by
    metis_tac[exprSimWordArgsTheory.expr_post_state] >>
  `log_arg_rel cenv cx sa sb es1 s1 (x,post_value_type cenv e1) v1` by
    fs[log_arg_rel_def, loweringPostsTheory.expr_post_def] >>
  drule_all bop_pair_first_post_kept >> strip_tac >>
  simp[] >> irule wordArgsPtrTheory.ghost_kept_wb_trans >> metis_tac[]
QED
