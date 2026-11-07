Theory bodyPtrIfExpNonwordBody
Ancestors
  bodyPtrIfExpNonwordCallerPremises bodyPtrIfExpWordCallerPremises
  bodyPtrIfExpConditionSource bodyPtrIfExpNonwordOutcome bodyPtrIfExpLocatedFinish
  bodyPtrIfExpWordTyping
  bodyPtrIfExpWordPrefix bodyPtrDefs bodyPtrPreds bodySim
  exprSimSource exprSimDefs exprSimWordArgs exprLoweringProps exprSimOperators
  gasSummaryComposePtr gasContext stmtFragPtr fragGasPathPtr
  vyperInterpreter vyperState loweringPosts compileEnv fragExec venomState
  list vyperAST fragGasSeqPtr

Theorem ifexp_selected_body_nonword_outcome_ptr:
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx a) /\
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx b) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (IfExp t c a b) es /\
  ~is_word_type t /\
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
    marks (INL (BoolV sel)) mid G1 tn1 (OK u) /\
  compile_expr cenv ty (if sel then a else b) se = (vv,sm) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) vv sm = (op,sx) /\
  fn_has_code se sm fn /\ fn_has_code sm sx fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv se /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  stmt_state_rel ctx fn cenv cx (mid with gas_obs := []) v0 /\
  ghost_inv d cenv cx (mid with gas_obs := []) G1 tn1 v0 /\
  ~v0.vs_halted /\ v0.vs_current_bb = se.cs_current_bb /\
  v0.vs_inst_idx = LENGTH se.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    (mid with gas_obs := [],v0,G1,tn1)
    (\res ee G tn z. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx fn cenv cx (if sel then a else b)
        (mid with gas_obs := []) se sx v0 ee v op z /\
      ptr_val_ok cx t v op G tn z /\ ptr_buf_ok cenv (IfExp t c a b) op G z /\
      ghost_inv d cenv cx ee G tn z /\
      ghost_kept cenv (mid with gas_obs := []) se G1 tn1 v0 G tn /\
      z.vs_current_bb = sx.cs_current_bb /\ z.vs_inst_idx = LENGTH sx.cs_current_insts)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `body_expr_ptr_ok cx a /\ body_expr_ptr_ok cx b` by
    metis_tac[ifexp_marked_condition_arm_body] >>
  `expr_body_pre cenv cx env a (mid with gas_obs := []) /\
   expr_body_pre cenv cx env b (mid with gas_obs := [])` by
    metis_tac[ifexp_marked_condition_arm_pre] >>
  `gas_admissible
     (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     expr_vv_res_ok (mid with gas_obs := [])` by
    (irule ifexp_branch_admissible >> goal_assum (drule_at Any) >>
     qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >> metis_tac[]) >>
  `expr_vv_sim_ptr d ctx PG fn cenv cx ty (if sel then a else b)
     (mid with gas_obs := [])` by
    (Cases_on `sel` >> simp[] >> metis_tac[body_expr_ptr_ok_def]) >>
  irule ifexp_selected_nonword_outcome_ptr >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `sel` >> gvs[] >> metis_tac[]
QED

Theorem ifexp_nonword_normal_continuation_ptr:
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx a) /\
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx b) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (IfExp t c a b) es /\
  ~is_word_type t /\ expr_type c = BaseT BoolT /\
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
    marks (INL (BoolV sel)) mid G1 tn1 (OK u) /\
  expr_post ctx fn cenv cx c es sa sc s0 (mid with gas_obs := []) (BoolV sel) cop u /\
  ptr_val_ok cx (expr_type c) (BoolV sel) cop G1 tn1 u /\
  ghost_inv d cenv cx (mid with gas_obs := []) G1 tn1 u /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
  compile_expr cenv ty (if sel then a else b) se = (av,sm) /\
  compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) av sm = (op,sx) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\ emit_inst JMP [Label xl] [] sy = ((),sz) /\
  se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  fn_has_code sj sn fn /\ fn_has_code se sm fn /\ fn_has_code sm sx fn /\
  fn_has_code sx sy fn /\ fn_has_code sy sz fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv se /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= se.cs_next_var /\
  sa.cs_next_id <= sc.cs_next_id /\ sc.cs_next_id <= se.cs_next_id /\
  sx.cs_next_id <= sb.cs_next_id /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (eval_expr cx (IfExp t c a b)) (es,s0,G0,tn0)
    (\res ee G tn z. ?tv. res = INL tv /\
      vv_post ctx fn cenv cx (IfExp t c a b) es sa sb s0 ee tv
        (LocatedValue t (mk_ptr (Var rv) LocMemory)) z /\
      ptr_vv_ok cx t tv (LocatedValue t (mk_ptr (Var rv) LocMemory)) ee G tn z /\
      ptr_buf_ok cenv (IfExp t c a b) (Var rv) G z /\
      ghost_inv d cenv cx ee G tn z /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL (BoolV sel),mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_type a = t /\ expr_type b = t` by
    (drule expr_body_pre_ifexp >> simp[] >> metis_tac[]) >>
  irule ifexp_selected_outcome_prefix_ptr >> goal_assum (drule_at Any) >>
  qexistsl_tac [`G1`,`tn1`,`jump_to (if sel then tl else el) u`] >>
  reverse conj_tac
  >- (irule ifexp_jnz_path_ptr >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule ifexp_located_arm_finish_ptr >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cop`,`if sel then a else b`,`op`,`sc`,`se`,`sx`,`sy`,`sz`,`BoolV sel`] >>
  simp[] >> conj_tac >- (Cases_on `sel` >> simp[]) >>
  irule ifexp_selected_body_nonword_outcome_ptr >> goal_assum (drule_at Any) >> simp[] >>
  simp[jump_to_def, ghost_inv_jump_to, stmt_state_rel_jump_to] >>
  `stmt_state_rel ctx fn cenv cx mid u` by fs[expr_post_def] >>
  `sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id` by decide_tac >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >> metis_tac[not_fresh_at_mono]
QED
