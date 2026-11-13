Theory bodyPtrIfExpLocatedFinish
Ancestors
  bodyPtrIfExpNonwordFinish bodyPtrIfExpWordFinish exprSimIfExp exprSimUnwrapProps
  exprSimUnwrap bodyPtrDefs loweringPosts exprSimDefs exprLowering context vyperAST
  vyperState gasSummaryComposePtr venomState finite_map loweringStateRelDefs
  compileEnv

Theorem ifexp_located_ptr_vv_read:
  ~is_word_type t /\ read_result cx tv ee = (INL v,ee) /\
  ptr_val_ok cx t v op G tn s ==>
  ptr_vv_ok cx t tv (LocatedValue t (mk_ptr op LocMemory)) ee G tn s
Proof
  simp[ptr_vv_ok_def, ptr_val_ok_def, mk_ptr_def] >> metis_tac[]
QED

(* The selected arm's vv_at, moved to the result variable it is assigned to. *)
Theorem ifexp_vv_at_root_frame[local]:
  vv_at cenv cx t sc sd es tv (LocatedValue t (mk_ptr op LocMemory)) u /\
  eval_operand op u = SOME w /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  sa.cs_next_id <= sc.cs_next_id /\ sd.cs_next_id <= sb.cs_next_id ==>
  vv_at cenv cx t sa sb es tv (LocatedValue t (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qabbrev_tac `ss = jump_to xl (update_var rv w u with vs_inst_idx := k)` >>
  `ss.vs_allocas = u.vs_allocas /\ lookup_var rv ss = SOME w /\
   (!x. x <> rv ==> lookup_var x ss = lookup_var x u)` by
    simp[Abbr `ss`, jump_to_def, update_var_def, lookup_var_def,
         FLOOKUP_UPDATE] >>
  `!n b sz. local_region cenv es.scopes ss n b sz <=>
            local_region cenv es.scopes u n b sz` by
    (rpt gen_tac >> simp[local_region_def] >> eq_tac >> rpt strip_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ u` mp_tac >>
  simp[vv_at_def, contextTheory.mk_ptr_def, eval_operand_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >> gvs[]
  >~ [`FLOOKUP u.vs_allocas aid = SOME _`]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
      `sa.cs_next_id <= aid /\ aid < sb.cs_next_id` by decide_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ifexp_root_finish_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_post H ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_post H ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  read_result cx tv ee = (INL v,ee) /\ expr_type e = t /\
  (~is_word_type t ==>
   vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u) /\
  eval_operand op u = SOME w /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  sd.cs_next_id <= sb.cs_next_id ==>
  vv_post H ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qpat_x_assum `_ ==> ~expr_has_effect e` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `IfExp t c a b`] ifexp_root_vv_post_of_expr_post_read)) >>
  conj_tac
  >- (strip_tac >>
      `vv_at cenv cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u`
        by fs[] >>
      irule ifexp_vv_at_root_frame >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`op`, `sc`, `sd`] >> simp[] >> decide_tac) >>
  qexists_tac `v` >> simp[] >>
  irule expr_post_ifexp >>
  `~not_fresh_at sa rv` by metis_tac[] >>
  simp[] >> metis_tac[]
QED

Theorem ifexp_located_arm_finish_ptr:
  expr_post H ctx fn ce cx c es sa s1 s0 es1 v1 cop tt /\
  post_value_type ce e = expr_type e /\
  expr_type e = t /\ ~is_word_type t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel H ctx fn ce cx es s0 /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy fn /\ fn_has_code sy sz fn /\ ~ctx_has_dalloca ctx /\
  gas_outcome_ptr D tops (ctx,fn) PG source (es1,jump_to lbl tt,G1,tn1)
    (\res ee G tn u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post H ctx fn ce cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      vv_at ce cx t sc sd ee tv (LocatedValue t (mk_ptr op LocMemory)) u /\
      ptr_val_ok cx t v op G tn u /\ ptr_buf_ok ce (IfExp t c a b) op G u /\
      ghost_inv H d ce cx ee G tn u /\
      ghost_kept ce es1 sc G1 tn1 (jump_to lbl tt) G tn /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts) R ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es1,jump_to lbl tt,G1,tn1)
    (\res ee G tn u. ?tv. res = INL tv /\
      vv_post H ctx fn ce cx (IfExp t c a b) es sa sb s0 ee tv
        (LocatedValue t (mk_ptr (Var rv) LocMemory)) u /\
      ptr_vv_ok cx t tv (LocatedValue t (mk_ptr (Var rv) LocMemory)) ee G tn u /\
      ptr_buf_ok ce (IfExp t c a b) (Var rv) G u /\
      ghost_inv H d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >>
  qpat_x_assum `_ ==> ~expr_has_effect e` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  irule ifexp_outcome_zero_suffix_ptr >>
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
  `vv_post H ctx fn ce cx (IfExp t c a b) es sa sb s0 ee tv
     (LocatedValue t (mk_ptr (Var rv) LocMemory))
     (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts))` by
    (`vv_post H ctx fn ce cx (IfExp t c a b) es sa sb s0 ee tv
        (if is_word_type t then StackValue t (Var rv)
         else LocatedValue t (mk_ptr (Var rv) LocMemory))
        (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts))`
       suffices_by simp[] >>
     irule ifexp_root_finish_post >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ptr_vv_ok _ _ _ (StackValue _ _) _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
  `ptr_vv_ok cx t tv (LocatedValue t (mk_ptr (Var rv) LocMemory)) ee
     (step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u))
     (step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn)
     (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts))` by
    (irule ifexp_located_ptr_vv_read >> metis_tac[]) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u)`,
    `step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn`,
    `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)`] >>
  conj_tac >- (irule ifexp_word_suffix_path_ptr >> simp[] >> metis_tac[]) >>
  simp[] >> simp[jump_to_def] >> gvs[jump_to_def]
QED
