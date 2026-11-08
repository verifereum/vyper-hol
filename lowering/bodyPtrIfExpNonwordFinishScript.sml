Theory bodyPtrIfExpNonwordFinish
Ancestors
  bodyPtrIfExpWordFinish bodyPtrIfExpAssignFrame bodyPtrDefs
  ptrDiscipline venomState venomInst finite_map
  loweringPosts vyperState stmtFragPtr exprSimPtrLiteralBuffer
  ghostPcTransportPtr exprSimIfExp exprSimDefs exprLowering vyperAST compileEnv

Theorem ifexp_assign_ptr_buf_ok:
  eval_operand src s = SOME w /\ ptr_buf_ok ce e src G s ==>
  ptr_buf_ok ce e (Var out)
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (update_var out w s)
Proof
  strip_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  simp[ptr_buf_ok_def, assign_result_value] >> strip_tac >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  strip_tac >> qexistsl_tac [`b`, `sz`] >>
  simp[SRULE [op_prov_def] assign_result_prov]
QED

Theorem ifexp_stack_vv_post_read:
  expr_post ctx fn ce cx e es sa sb s0 ee v op s /\
  read_result cx tv ee = (INL v,ee) ==>
  vv_post ctx fn ce cx e es sa sb s0 ee tv (StackValue tag op) s
Proof
  simp[expr_post_def, vv_post_def, vv_holds_def, vv_at_def] >>
  metis_tac[]
QED

Theorem ifexp_nonword_suffix_ghost:
  eval_operand op u = SOME w /\
  read_result cx tv ee = (INL v,ee) /\ ptr_val_ok cx t v op G tn u /\
  ptr_buf_ok ce e op G u /\
  ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> rv) ==>
  ptr_vv_ok cx t tv (StackValue t (Var rv)) ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ptr_buf_ok ce e (Var rv)
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ghost_inv d ce cx ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ghost_kept ce es sa G0 tn0 s0
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
Proof
  strip_tac >> conj_tac
  >- (simp[ptr_vv_ok_def] >>
      drule_all assign_ptr_val_ok >>
      disch_then (qspecl_then [`rv`, `id`, `PG`] mp_tac) >>
      simp[ptr_val_ok_def, ptr_mem_ok_def, jump_to_def, lookup_var_def]) >>
  conj_tac
  >- (drule_all ifexp_assign_ptr_buf_ok >>
      simp[ptr_buf_ok_def, jump_to_def, lookup_var_def]) >>
  conj_tac
  >- (simp[jump_to_def, ghost_inv_jump_to,
           SRULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize] >>
      irule assign_ghost_inv >> simp[] >> metis_tac[]) >>
  irule assign_ghost_kept >> simp[] >> metis_tac[]
QED

Theorem ifexp_nonword_arm_finish_ptr:
  expr_post ctx fn ce cx c es sa s1 s0 es1 v1 cop tt /\
  expr_type e = t /\ ~is_word_type t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx fn ce cx es s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy fn /\ fn_has_code sy sz fn /\ ~ctx_has_dalloca ctx /\
  gas_outcome_ptr D tops (ctx,fn) PG source (es1,jump_to lbl tt,G1,tn1)
    (\res ee G tn u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx fn ce cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      ptr_val_ok cx t v op G tn u /\ ptr_buf_ok ce (IfExp t c a b) op G u /\
      ghost_inv d ce cx ee G tn u /\
      ghost_kept ce es1 sc G1 tn1 (jump_to lbl tt) G tn /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts) R ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es1,jump_to lbl tt,G1,tn1)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post ctx fn ce cx (IfExp t c a b) es sa sb s0 ee tv (StackValue t (Var rv)) u /\
      ptr_vv_ok cx t tv (StackValue t (Var rv)) ee G tn u /\
      ptr_buf_ok ce (IfExp t c a b) (Var rv) G u /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >> irule ifexp_outcome_zero_suffix_ptr >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?w. eval_operand op u = SOME w` by metis_tac[expr_post_def, expr_val_rel_def] >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
  `ghost_kept ce es sa G0 tn0 s0 G tn` by
    (irule ifexp_condition_arm_ghost_kept >> metis_tac[]) >>
  `!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> rv` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> rv)` by metis_tac[] >>
  drule_all ifexp_nonword_suffix_ghost >>
  disch_then (qspecl_then [`xl`,`LENGTH sy.cs_current_insts`,`sd.cs_next_id`,`PG`] strip_assume_tac) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u)`,
    `step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn`,
    `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)`] >>
  conj_tac >- (irule ifexp_word_suffix_path_ptr >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule ifexp_stack_vv_post_read >> goal_assum (drule_at Any) >>
      irule expr_post_ifexp >> simp[] >> metis_tac[]) >>
  simp[jump_to_def] >> gvs[jump_to_def]
QED
