Theory bodyPtrSubscriptOperands
Ancestors
  bodyPtrDefs bodyPtrSubscriptTransport gasSummaryComposePtr loweringPosts

Theorem expr_post_ghost_kept_ptr_covers:
  expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 sz ==>
  ptr_covers G tn p t sz
Proof
  rpt strip_tac >>
  irule ghost_kept_ptr_covers >>
  goal_assum (drule_at Any) >>
  gvs[expr_post_def, ptr_covers_def] >> metis_tac[]
QED

Theorem expr_sim_ptr_captured_ptr_covers:
  expr_sim_ptr d ctx PG func cenv cx ty idx es /\
  lower_value compile_expr cenv ty idx sa = (op, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 sz ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (eval_expr cx idx) (read_result cx)) (es, s0, G0, tn0)
    (\res ee G tn t. ?v. res = INL v /\
      expr_post ctx func cenv cx idx es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type idx) v op G tn t /\
      (~is_word_type (expr_type idx) ==> ptr_buf_ok cenv idx op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      ptr_covers G tn p t sz)
    (\res ee gt r. expr_exit res r)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >>
  simp[] >> metis_tac[expr_post_ghost_kept_ptr_covers]
QED
