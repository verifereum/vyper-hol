Theory typedWordArgsPostPtr
Ancestors
  wordArgsPtr exprSimWordArgs exprSimPrecompiles bodyPtrDefs loweringPosts
  exprLoweringProps gasSummaryComposePtr fragGasPathPtr stmtFragPtr

(* Package the typed S1 list post and its ghost frame once, so list
   composition and callers need not unfold either implementation. *)
Definition typed_args_post_ptr_def:
  typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee args xs vs G tn s <=>
    typed_args_post ctx func cenv cx es sa s0 ee args xs vs s /\
    ghost_inv d cenv cx ee G tn s /\
    EVERY (\op. op_taint tn op = {}) xs /\
    ghost_kept cenv es sa G0 tn0 s0 G tn
End

Theorem typed_args_post_ptr_nil:
  stmt_state_rel ctx func cenv cx ee s /\ ghost_inv d cenv cx ee G tn s ==>
  typed_args_post_ptr d ctx func cenv cx ee sa s G tn ee [] [] [] G tn s
Proof
  simp[typed_args_post_ptr_def, typed_args_post_def,
       wb_frame_refl, ghost_kept_refl]
QED

Theorem typed_args_post_ptr_cons:
  expr_post ctx func cenv cx e es sa s1 s0 es1 v x t /\
  typed_args_post_ptr d ctx func cenv cx es1 s1 t G1 tn1 ee args xs vs G tn u /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv s1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  ptr_val_ok cx (expr_type e) v x G1 tn1 t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 ==>
  typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee
    (e::args) (x::xs) (v::vs) G tn u
Proof
  rewrite_tac[typed_args_post_ptr_def] >> strip_tac >>
  conj_tac >- (irule typed_args_post_cons >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (gvs[typed_args_post_def, ptr_val_ok_def] >>
      `?w. eval_operand x t = SOME w` by
        metis_tac[expr_post_def, expr_val_rel_def] >>
      drule_all word_operand_frame >> simp[]) >>
  `wb_frame cenv es es1 sa s0 t` by (gvs[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  drule_all ghost_kept_wb_trans >> simp[]
QED

Theorem lower_typed_args_nil_sim_ptr:
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  ghost_inv d cenv cx es G0 tn0 s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_exprs cx [])
    (es,s0,G0,tn0)
    (\rr ee G tn t. ?vs. rr = INL vs /\
       typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee [] [] vs G tn t /\
       t.vs_current_bb = sa.cs_current_bb /\
       t.vs_inst_idx = LENGTH sa.cs_current_insts)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> rewrite_tac[gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL []`, `es`, `G0`, `tn0`, `OK s0`] >>
  conj_tac >- (irule eval_exprs_nil_marked_ptr >> simp[]) >>
  simp[typed_args_post_ptr_def, typed_args_post_def,
       stmt_state_rel_gas_obs, ghost_inv_gas_obs,
       wb_frame_refl, ghost_kept_refl]
QED
