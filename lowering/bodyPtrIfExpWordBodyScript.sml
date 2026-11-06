Theory bodyPtrIfExpWordBody
Ancestors
  bodyPtrIfExpWordCallerPremises bodyPtrIfExpConditionSource
  bodyPtrIfExpWordTyping bodyPtrIfExpWordOutcome bodyPtrIfExpWordFinish
  bodyPtrIfExpWordPrefix bodyPtrDefs bodyPtrPreds bodySim
  exprSimSource exprSimDefs exprSimWordArgs exprLoweringProps exprSimOperators
  exprPtrUnwrap gasSummaryComposePtr gasContext stmtFragPtr fragGasPathPtr
  vyperInterpreter vyperState loweringPosts compileEnv fragExec venomState
  list vyperAST fragGasSeqPtr

Theorem ifexp_selected_body_word_outcome_ptr:
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx a) /\
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx b) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (IfExp t c a b) es /\
  is_word_type t /\
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
    (bind (eval_expr cx c) (read_result cx)) (es,s0,G0,tn0)
    marks (INL (BoolV sel)) mid G1 tn1 (OK u) /\
  compile_expr cenv ty (if sel then a else b) se = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sx) /\
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
      ptr_val_ok cx (expr_type (if sel then a else b)) v op G tn z /\
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
  `expr_type a = t /\ expr_type b = t` by
    (drule expr_body_pre_ifexp >> simp[] >> metis_tac[]) >>
  `gas_admissible
     (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     expr_vv_res_ok (mid with gas_obs := [])` by
    (irule ifexp_branch_admissible >> goal_assum (drule_at Any) >>
     qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     metis_tac[]) >>
  `expr_vv_sim_ptr d ctx PG fn cenv cx ty (if sel then a else b)
     (mid with gas_obs := [])` by
    (Cases_on `sel` >> simp[] >> metis_tac[body_expr_ptr_ok_def]) >>
  irule ifexp_selected_word_outcome_ptr >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `sel` >> gvs[] >> metis_tac[]
QED

Theorem ifexp_word_normal_continuation_ptr:
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx a) /\
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx b) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (IfExp t c a b) es /\
  is_word_type t /\ expr_type c = BaseT BoolT /\
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
  unwrap_value cenv av sm = (op,sx) /\
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
      vv_post ctx fn cenv cx (IfExp t c a b) es sa sb s0 ee tv (StackValue t (Var rv)) z /\
      ptr_vv_ok cx t tv (StackValue t (Var rv)) ee G tn z /\
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
  irule ifexp_selected_outcome_prefix_ptr >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`G1`,`tn1`,`jump_to (if sel then tl else el) u`] >>
  reverse conj_tac
  >- (irule ifexp_jnz_path_ptr >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule ifexp_word_arm_finish_ptr >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cop`,`if sel then a else b`,`op`,`sc`,`se`,`sx`,`sy`,`sz`,`BoolV sel`] >>
  simp[] >> conj_tac >- (Cases_on `sel` >> simp[]) >>
  irule ifexp_selected_body_word_outcome_ptr >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[jump_to_def, ghost_inv_jump_to, stmt_state_rel_jump_to] >>
  `stmt_state_rel ctx fn cenv cx mid u` by fs[expr_post_def] >>
  `sa.cs_next_var <= se.cs_next_var /\ sa.cs_next_id <= se.cs_next_id` by decide_tac >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem ifexp_word_framed_vv_ptr:
  is_word_type t /\
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx a) /\
  (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx b) /\
  body_expr_ptr_ok cx c /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (IfExp t c a b) es ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty (IfExp t c a b) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  `!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
     cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
     cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `expr_type c = BaseT BoolT /\ expr_body_pre cenv cx env c es` by
    (drule expr_body_pre_ifexp >> simp[] >> metis_tac[]) >>
  `expr_sim_ptr d ctx PG fn cenv cx (BaseT BoolT) c es` by
    metis_tac[body_expr_ptr_ok_def] >>
  `?cop sc. lower_value compile_expr cenv (BaseT BoolT) c sa = (cop,sc) /\
     fn_has_code sa sc fn` by
    (drule_all ifexp_word_code_layout >>
     disch_then (qspec_then `T` mp_tac) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >>
  disch_then (strip_assume_tac o REWRITE_RULE
    [gas_outcome_ptr_def, gas_summary_ptr_at_marked])
  >- (gvs[] >> suspend "normal")
  >- (irule ifexp_condition_exit_ptr >> metis_tac[]) >>
  irule ifexp_condition_exempt_ptr >> metis_tac[]
QED

Resume ifexp_word_framed_vv_ptr[normal]:
  `bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,es_end with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[APPEND_NIL]) >>
  `?sel. v = BoolV sel` by
    (irule ifexp_condition_bool >> goal_assum (drule_at Any) >> metis_tac[]) >> gvs[] >>
  drule_all ifexp_word_code_layout >>
  disch_then (qspec_then `sel` strip_assume_tac) >> gvs[] >>
  `~t'.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  irule gas_outcome_ptr_conseq >>
  irule_at Any ifexp_word_normal_continuation_ptr >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst ASSIGN _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst JMP _ _ _ = _`)) >> simp[] >>
  qexistsl_tac [`tops`,`env`,`d`] >> simp[expr_type_def] >> metis_tac[]
QED

Finalise ifexp_word_framed_vv_ptr

Theorem ifexp_word_expr_ptr_ok:
  !cx t c a b.
    is_word_type t /\
    (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx a) /\
    (!s raw ee. eval_expr cx c s = (INL raw,ee) ==> body_expr_ptr_ok cx b) /\
    body_expr_ptr_ok cx c ==>
    body_expr_ptr_ok cx (IfExp t c a b)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[body_expr_ptr_ok_def] >> rpt strip_tac >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty (IfExp t c a b) es` by
    (irule ifexp_word_framed_vv_ptr >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[] >> irule expr_sim_ptr_of_vv >> goal_assum (drule_at Any) >> metis_tac[]
QED
