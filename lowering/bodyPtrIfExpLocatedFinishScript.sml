Theory bodyPtrIfExpLocatedFinish
Ancestors
  bodyPtrIfExpNonwordFinish exprSimIfExp exprSimUnwrapProps exprSimUnwrap
  bodyPtrDefs loweringPosts exprSimDefs exprLowering context vyperAST vyperState
  gasSummaryComposePtr

Theorem ifexp_located_vv_post_read:
  ~is_word_type (expr_type e) /\
  expr_post ctx fn ce cx e es sa sb s0 ee v (Var rv) s /\
  read_result cx tv ee = (INL v,ee) ==>
  vv_post ctx fn ce cx e es sa sb s0 ee tv
    (LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  strip_tac >> drule vv_post_read_result >> disch_then (fn th => fs[th]) >>
  drule vv_post_of_expr_post >> simp[]
QED

Theorem ifexp_located_ptr_vv_read:
  ~is_word_type t /\ read_result cx tv ee = (INL v,ee) /\
  ptr_val_ok cx t v op G tn s ==>
  ptr_vv_ok cx t tv (LocatedValue t (mk_ptr op LocMemory)) ee G tn s
Proof
  simp[ptr_vv_ok_def, ptr_val_ok_def, mk_ptr_def] >> metis_tac[]
QED

Theorem ifexp_stack_to_located_post:
  ~is_word_type (expr_type e) /\
  vv_post ctx fn ce cx e es sa sb s0 ee tv (StackValue tag (Var rv)) s ==>
  vv_post ctx fn ce cx e es sa sb s0 ee tv
    (LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  strip_tac >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (gvs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
  irule ifexp_located_vv_post_read >> goal_assum (drule_at Any) >> simp[] >>
  irule expr_post_of_vv_post_stack >> metis_tac[vv_post_read_result]
QED

Theorem ifexp_stack_to_located_outcome_ptr:
  ~is_word_type (expr_type e) /\
  gas_outcome_ptr D tops (ctx,fn) PG source (es1,z,G1,tn1)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post ctx fn ce cx e es sa sb s0 ee tv (StackValue (expr_type e) (Var rv)) u /\
      ptr_vv_ok cx (expr_type e) tv (StackValue (expr_type e) (Var rv)) ee G tn u /\
      ptr_buf_ok ce e (Var rv) G u /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es1,z,G1,tn1)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post ctx fn ce cx e es sa sb s0 ee tv
        (LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) u /\
      ptr_vv_ok cx (expr_type e) tv
        (LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) ee G tn u /\
      ptr_buf_ok ce e (Var rv) G u /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexists_tac `tv` >> simp[] >>
  conj_tac >- (irule ifexp_stack_to_located_post >> metis_tac[]) >>
  qpat_x_assum `ptr_vv_ok _ _ _ (StackValue _ _) _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
  irule ifexp_located_ptr_vv_read >> metis_tac[]
QED

Theorem ifexp_located_arm_finish_ptr:
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
      vv_post ctx fn ce cx (IfExp t c a b) es sa sb s0 ee tv
        (LocatedValue t (mk_ptr (Var rv) LocMemory)) u /\
      ptr_vv_ok cx t tv (LocatedValue t (mk_ptr (Var rv) LocMemory)) ee G tn u /\
      ptr_buf_ok ce (IfExp t c a b) (Var rv) G u /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >>
  irule (SRULE [expr_type_def]
    (Q.INST [`e` |-> `IfExp t c a b`] ifexp_stack_to_located_outcome_ptr)) >>
  conj_tac >- simp[] >>
  irule ifexp_nonword_arm_finish_ptr >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
