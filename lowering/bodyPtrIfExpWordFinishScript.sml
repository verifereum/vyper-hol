Theory bodyPtrIfExpWordFinish
Ancestors
  bodyPtrIfExpAssign bodyPtrIfExpAssignFrame ifJumpPtr
  fragGasPathPtr emitHelperProps venomState venomInst ptrSafeRun
  bodyPtrDefs stmtFragPtr ghostPcTransportPtr exprSimIfExp exprSimDefs
  loweringPosts exprLowering context vyperAST vyperState compileEnv loweringStateRelDefs
  wordArgsPtr exprSimWordArgs exprSimPtrLiteralBuffer gasSummaryComposePtr fragGasSeqPtr
  vyperStorageTrace vyperStorageFootprint fragExec

Theorem ifexp_word_suffix_path_ptr:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy fn /\ fn_has_code sy sz fn /\ ~ctx_has_dalloca ctx /\
  ~u.vs_halted /\ u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ eval_operand op u = SOME w ==>
  gas_path_ptr D 0 ctx fn PG G tn u 0
    (step_prov PG G (mk_inst sx.cs_next_id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst sx.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  strip_tac >> drule_all emit_assign_zero_path_ptr >> strip_tac >>
  `sy.cs_current_bb = sx.cs_current_bb /\ sz.cs_blocks = sy.cs_blocks /\
   sz.cs_current_bb = sy.cs_current_bb /\
   sz.cs_current_insts = sy.cs_current_insts ++
     [mk_inst sy.cs_next_id JMP [Label xl] []]` by
    metis_tac[emit_inst_extends] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  first_x_assum (qspecl_then [`tn`,`PG`,`G`,`D`] assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule if_emit_jump_zero_path_ptr >> simp[update_var_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ifexp_word_vv_post_read[local]:
  is_word_type (expr_type e) /\
  expr_post H ctx fn cenv cx e es sa sb s0 ee v (Var rv) s /\
  read_result cx tv ee = (INL v,ee) ==>
  vv_post H ctx fn cenv cx e es sa sb s0 ee tv (StackValue (expr_type e) (Var rv)) s
Proof
  rw[expr_post_def, vv_post_def] >>
  gvs[vv_holds_def, vv_at_def] >>
  fs[expr_val_rel_def, expr_val_at_def] >>
  rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_word_finish_post:
  expr_post H ctx fn cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_post H ctx fn cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  read_result cx tv ee = (INL v,ee) /\ expr_type e = t /\ is_word_type t /\
  eval_operand op u = SOME w /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx fn cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  sd.cs_next_id <= sb.cs_next_id ==>
  vv_post H ctx fn cenv cx (IfExp t c a b) es sa sb s0 ee tv (StackValue t (Var rv))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  qpat_x_assum `_ ==> ~expr_has_effect e` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  irule (SRULE [expr_type_def]
    (Q.INST [`e` |-> `IfExp t c a b`] ifexp_word_vv_post_read)) >>
  goal_assum (drule_at Any) >> simp[] >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_word] >>
  irule expr_post_ifexp >> simp[] >> metis_tac[]
QED

Theorem ifexp_condition_arm_ghost_kept:
  expr_post H ctx fn cenv cx c es sa s1 s0 es1 v1 cop tt /\
  stmt_state_rel H ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sc G1 tn1 (jump_to lbl tt) G tn ==>
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  `wb_frame cenv es es1 sa s0 (jump_to lbl tt)` by
    (qspecl_then [`cenv`,`es`,`es1`,`sa`,`s0`,`tt`,`sa`,`jump_to lbl tt`]
       irule wb_frame_readonly_tail >>
     simp[jump_to_def, lookup_var_def] >> metis_tac[expr_post_frame]) >>
  drule_all ghost_kept_wb_trans >> simp[]
QED

Theorem ifexp_word_suffix_ghost:
  is_word_type t /\ eval_operand op u = SOME w /\
  read_result cx tv ee = (INL v,ee) /\ ptr_val_ok cx t v op G tn u /\
  ghost_inv H d cenv cx ee G tn u /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  (!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> rv) ==>
  ptr_vv_ok cx t tv (StackValue t (Var rv)) ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ghost_inv H d cenv cx ee
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
    (jump_to xl (update_var rv w u with vs_inst_idx := k)) /\
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id ASSIGN [op] [rv]) (update_var rv w u))
    (step_taint (mk_inst id ASSIGN [op] [rv]) u (update_var rv w u) tn)
Proof
  strip_tac >> conj_tac
  >- (simp[ptr_vv_ok_def] >>
      drule_all assign_ptr_val_ok >> simp[ptr_val_ok_def]) >>
  conj_tac
  >- (simp[jump_to_def, ghost_inv_jump_to,
           SRULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize] >>
      irule assign_ghost_inv >> simp[] >> metis_tac[]) >>
  irule assign_ghost_kept >> simp[] >> metis_tac[]
QED

Theorem ifexp_outcome_zero_suffix_ptr:
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es,s0,G0,tn0) P R /\
  (!marks res ee G tn u.
    (!tail. source (es with gas_obs :=
       gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res,ee with gas_obs := tail)) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H res ee G tn u) /\
    ~u.vs_halted ==>
    ?G' tn' v. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_path_ptr (D H) 0 ctx fn PG G tn u 0 G' tn' (OK v) /\
      Q H res ee G' tn' v) ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es,s0,G0,tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[])
  >- (disj2_tac >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def]) >>
      rewrite_tac[gas_summary_ptr_at_def] >>
      reverse (Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`)
      >- (qexistsl_tac [`res`,`es_end`,`G`,`tn`,`r`] >> simp[] >> metis_tac[]) >>
      pop_assum strip_assume_tac >>
      reverse (Cases_on `?u. r = OK u`)
      >- (qexistsl_tac [`res`,`es_end`,`G`,`tn`,`r`] >> simp[] >> metis_tac[]) >>
      pop_assum strip_assume_tac >> gvs[exit_result_def] >>
      `~u.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
      qpat_x_assum `!marks res ee G tn u. _`
        (qspecl_then [`marks`,`res`,`es_end with gas_obs := []`,`G`,`tn`,`u`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
      qexistsl_tac [`res`,`es_end`,`G'`,`tn'`,`OK v`] >> simp[] >>
      qx_gen_tac `H2` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ _ _ ==>
        gas_path_ptr _ _ _ _ _ G tn u _ _ _ _ /\ _`
        (qspec_then `H2` mp_tac) >>
      impl_tac >- simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `gas_path_ptr (D H2) 0 ctx fn PG G0 tn0 s0 (LENGTH marks) G tn (OK u)`
        by metis_tac[] >>
      simp[] >>
      `LENGTH marks = LENGTH marks + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem ifexp_word_arm_finish_ptr:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx fn cenv cx c es sa s1 s0 es1 v1 cop tt /\
    stmt_state_rel H ctx fn cenv cx es s0) /\
  expr_type e = t /\ is_word_type t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ storage_trace_frame source /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  (~expr_has_effect (IfExp t c a b) ==> ~expr_has_effect e) /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy fn /\ fn_has_code sy sz fn /\ ~ctx_has_dalloca ctx /\
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es1,jump_to lbl tt,G1,tn1)
    (\H res ee G tn u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post H ctx fn cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      ptr_val_ok cx (expr_type e) v op G tn u /\ ghost_inv H d cenv cx ee G tn u /\
      ghost_kept cenv es1 sc G1 tn1 (jump_to lbl tt) G tn /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts) R ==>
  gas_outcome_ptr D tops (ctx,fn) PG cx st0 source (es1,jump_to lbl tt,G1,tn1)
    (\H res ee G tn u. ?tv. res = INL tv /\
      vv_post H ctx fn cenv cx (IfExp t c a b) es sa sb s0 ee tv (StackValue t (Var rv)) u /\
      ptr_vv_ok cx t tv (StackValue t (Var rv)) ee G tn u /\
      ghost_inv H d cenv cx ee G tn u /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >>
  qpat_x_assum `_ ==> ~expr_has_effect e` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  irule ifexp_outcome_zero_suffix_ptr >>
  goal_assum (drule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >>
  `?w. eval_operand op u = SOME w` by
    (qpat_x_assum `!H. valid_horizon _ _ _ ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sd.cs_next_id ASSIGN [op] [rv]) (update_var rv w u)`,
    `step_taint (mk_inst sd.cs_next_id ASSIGN [op] [rv]) u (update_var rv w u) tn`,
    `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)`] >>
  qx_gen_tac `H2` >> strip_tac >>
  `valid_horizon cx st0 H2 es1.storage_trace` by
    (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
     `valid_horizon cx st0 H2 (ee with gas_obs := []).storage_trace` by simp[] >>
     drule_all valid_horizon_frame >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ _ ee.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ es1.storage_trace ==> _`
    (qspec_then `H2` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G tn` by
    (irule (INST_TYPE [alpha |-> ``:256``] ifexp_condition_arm_ghost_kept) >> simp[] >>
     qexistsl_tac [`G1`,`H2`,`c`,`cop`,`ctx`,`cx`,`es1`,`fn`,`lbl`,
       `s1`,`sc`,`tn1`,`tt`,`v1`] >> simp[]) >>
  `!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> rv` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> rv) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> rv)` by metis_tac[] >>
  fs[] >> drule_all (SRULE [] ifexp_word_suffix_ghost) >>
  disch_then (qspecl_then [`sb.cs_current_bb`,`LENGTH sy.cs_current_insts`,`sd.cs_next_id`,`PG`] strip_assume_tac) >>
  conj_tac >- (irule ifexp_word_suffix_path_ptr >> simp[] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule ifexp_word_finish_post >> simp[] >> metis_tac[]) >>
  simp[jump_to_def] >> gvs[jump_to_def]
QED
