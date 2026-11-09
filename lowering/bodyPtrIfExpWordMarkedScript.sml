Theory bodyPtrIfExpWordMarked
Ancestors
  bodyPtrIfExpWordUnwrap bodyPtrIfExpWordTyping bodyPtrIfExpSource
  bodyPtrIfExpConditionalSource
  bodyPtrDefs gasSummaryComposePtr fragGasSeqPtr exprSimUnwrap
  exprOperandVar exprSimSource exprLoweringProps
  vyperEvalExprPreservesScopesDom vyperStatePreservation vyperInterpreter
  vyperState loweringPosts exprSimDefs gasContext

Theorem ifexp_raw_marked_word_unwrap:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  compile_expr cenv ty e sa = (vv,sm) /\ unwrap_value cenv vv sm = (op,sb) /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  vv_post ctx fn cenv cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv (ee with gas_obs := []) G tn s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u G1 tn1.
    read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
    expr_post ctx fn cenv cx e es sa sb s0 (ee with gas_obs := []) v op u /\
    ptr_val_ok cx (expr_type e) v op G1 tn1 u /\
    ghost_inv d cenv cx (ee with gas_obs := []) G1 tn1 u /\
    ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?v. read_result cx raw (ee with gas_obs := []) =
       (INL v,ee with gas_obs := [])` by
    (Cases_on `read_result cx raw (ee with gas_obs := [])` >>
     rename1 `_ = (res,st)` >>
     `st = ee with gas_obs := []` by metis_tac[read_result_state] >> gvs[] >>
     Cases_on `res` >> metis_tac[vv_post_failed_read]) >>
  drule_all ifexp_marked_arm_read_typed >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[compile_expr_extends] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `~s.vs_halted` by
    (gvs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    suspend "scopes" >>
  qexists_tac `v` >> simp[] >> irule ifexp_word_unwrap_suffix >> metis_tac[]
QED

Resume ifexp_raw_marked_word_unwrap[scopes]:
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule eval_expr_preserves_scopes_dom >> simp[]
QED

Finalise ifexp_raw_marked_word_unwrap

Theorem ifexp_raw_marked_word_then:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK u) /\
  (!tail. conditional_result cx raw (ee with gas_obs := tail) =
          (INL tv,ee with gas_obs := tail)) ==>
  gas_marked_exec_ptr D (ctx,fn) PG
    (bind (eval_expr cx e) (conditional_result cx)) (es,s0,G0,tn0)
    marks (INL tv) ee G1 tn1 (OK u)
Proof
  strip_tac >>
  `marks = marks ++ []` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_marked_exec_ptr_bind_normal >> goal_assum (drule_at Any) >>
  simp[gas_marked_exec_ptr_def]
QED

Theorem ifexp_raw_marked_exception:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks res ee G tn r /\ expr_exit res r ==>
  gas_marked_exec_ptr D (ctx,fn) PG
    (bind (eval_expr cx e) (conditional_result cx)) (es,s0,G0,tn0)
    marks res ee G tn r
Proof
  strip_tac >> Cases_on `res`
  >- (Cases_on `r` >> gvs[expr_exit_def]) >>
  irule gas_marked_exec_ptr_bind_exception >> goal_assum (drule_at Any)
QED


Theorem ifexp_marked_conditional_source:
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx e) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  gas_admissible (bind (eval_expr cx e) (conditional_result cx)) expr_vv_res_ok es /\
  read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) ==>
  ?tv. (!tail. conditional_result cx raw (ee with gas_obs := tail) =
          (INL tv,ee with gas_obs := tail)) /\
       read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := [])
Proof
  strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  Cases_on `conditional_result cx raw (ee with gas_obs := [])` >>
  rename1 `_ = (res,st)` >>
  `expr_vv_res_ok res` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def]) >>
  drule_all ifexp_conditional_source_success >> simp[]
QED
