(* Pointer and capacity posts remain aligned with operands and expressions. *)
Theory logArgsPostPtr
Ancestors
  logValueFramePtr logGhostFramePtr stmtSimLogArgs bodyPtrDefs
  exprSimProps exprSimWordArgs loweringPosts compileEnv venomState list

Theorem log_argument_ptr_buf_kept:
  ptr_buf_ok cenv e x G1 t /\ expr_val_rel cx (expr_type e) v x t /\
  wb_frame cenv es1 sm t u /\ ghost_kept cenv es1 sm G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) ==>
  ptr_buf_ok cenv e x G2 u
Proof
  strip_tac >> irule ptr_buf_ok_frame >> qexistsl_tac [`G1`,`t`] >> simp[] >>
  `?w. eval_operand x t = SOME w` by gvs[expr_val_rel_def] >>
  `eval_operand x u = SOME w` by (drule_all log_frame_operand >> simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[ghost_kept_def]
QED

Theorem log_args_ptr_vals_cons:
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  expr_val_rel cx (expr_type e) v x t /\
  expr_val_at cenv cx (expr_type e) sa sm es1 v x t /\
  wb_frame cenv es1 sm t u /\ ghost_kept cenv es1 sm G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  log_arg_clear cenv cx (expr_type e) v /\
  LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G2 tn2 u) ys vs ==>
  LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G2 tn2 u)
    ((x,expr_type e)::ys) (v::vs)
Proof
  strip_tac >> simp[] >> drule_all log_argument_ptr_val_kept >> simp[]
QED

Theorem log_args_ptr_bufs_cons:
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G1 t) /\
  expr_val_rel cx (expr_type e) v x t /\
  wb_frame cenv es1 sm t u /\ ghost_kept cenv es1 sm G1 tn1 t G2 tn2 /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  LIST_REL (\e p. ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (FST p) G2 u) args ys ==>
  LIST_REL (\e p. ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (FST p) G2 u) (e::args) ((x,expr_type e)::ys)
Proof
  strip_tac >> simp[] >> strip_tac >> gvs[] >>
  drule_all log_argument_ptr_buf_kept >> simp[]
QED

Theorem log_args_post_ptr_cons:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sb.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ (!l. x <> Label l) /\
  expr_sim_inv cenv cx env0 es0 /\ expr_type e = BaseT bt /\
  post_value_type cenv e = expr_type e /\
  expr_post ctx func cenv cx e es sa sm s0 es1 v x t /\
  log_args_post ctx func cenv cx es1 sm sb t es' ys vs u /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G1 t) /\
  LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G2 tn2 u) ys vs /\
  LIST_REL (\e p. ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (FST p) G2 u) args ys /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sm G1 tn1 t G2 tn2 ==>
  log_args_post ctx func cenv cx es sa sb s0 es'
    ((x,expr_type e)::ys) (v::vs) u /\
  LIST_REL (\p v. ptr_val_ok cx (SND p) v (FST p) G2 tn2 u)
    ((x,expr_type e)::ys) (v::vs) /\
  LIST_REL (\e p. ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e (FST p) G2 u) (e::args) ((x,expr_type e)::ys) /\
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `wb_frame cenv es sa s0 t` by (drule_all expr_post_frame >> simp[]) >>
  `wb_frame cenv es1 sm t u` by (drule_all log_args_post_frame >> simp[]) >>
  `expr_val_rel cx (expr_type e) v x t /\
   expr_val_at cenv cx (expr_type e) sa sm es1 v x t` by
    gvs[expr_post_def] >>
  `log_arg_clear cenv cx (expr_type e) v` by
    (gvs[] >> irule log_arg_clear_base >> metis_tac[]) >>
  conj_tac >- (drule_all log_args_post_cons >> simp[]) >>
  conj_tac >- (drule_all log_args_ptr_vals_cons >> simp[]) >>
  conj_tac >- (drule_all log_args_ptr_bufs_cons >> simp[]) >>
  drule_all ghost_kept_wb_trans >> simp[]
QED
