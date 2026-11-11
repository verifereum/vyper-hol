Theory bodyPtrIfExpNonwordMarked
Ancestors bodyPtrIfExpNonwordSuffix bodyPtrIfExpWordMarked
  bodyPtrIfExpObservationFrame exprSimPtrLiteralBuffer
  bodyPtrDefs bodySim exprSimDefs exprSimProps exprSimSource
  gasSummaryComposePtr fragGasSeqPtr vyperInterpreter vyperState
  vyperEvalExprPreservesScopesDom exprSimUnwrap exprSimWordArgs

Theorem ifexp_raw_marked_nonword_suffix:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty c a b) es_outer /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  ~is_word_type ty /\ ~ce.ce_is_ctor /\
  compile_expr ce rty arm sa = (vv,sm) /\
  compile_ifexp_arm ce ty (lowered_value_type ce arm) vv sm = (op,sd) /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx arm) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx arm es sa sm s0 (ee with gas_obs := []) raw vv s /\
  ptr_vv_ok cx (expr_type arm) raw vv (ee with gas_obs := []) G tn s /\
  (!tag src. vv = StackValue tag src /\ ~is_word_type (expr_type arm) ==>
    ptr_buf_ok ce arm src G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce arm p.ptr_operand G s) /\
  ghost_inv d ce cx (ee with gas_obs := []) G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\ local_ptrs_reserved ce sa /\
  fn_has_code sm sd fn /\ fn_inst_ids_distinct fn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u H tt.
    read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK u) /\
    expr_post ctx fn ce cx arm es sa sd s0 (ee with gas_obs := []) v op u /\
    ptr_val_ok cx ty v op H tt u /\ ptr_buf_ok ce (IfExp ty c a b) op H u /\
    ghost_inv d ce cx (ee with gas_obs := []) H tt u /\
    ghost_kept ce es sa G0 tn0 s0 H tt /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  strip_tac >>
  `?v. read_result cx raw (ee with gas_obs := []) =
       (INL v,ee with gas_obs := [])` by
    (Cases_on `read_result cx raw (ee with gas_obs := [])` >>
     rename1 `_ = (res,st)` >>
     `st = ee with gas_obs := []` by metis_tac[read_result_state] >> gvs[] >>
     Cases_on `res` >> metis_tac[vv_post_failed_read]) >>
  `eval_expr cx arm (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `~s.vs_halted` by
    (gvs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  gvs[] >>
  drule_at (Pat `eval_expr _ _ _ = _`) ifexp_nonword_arm_suffix >>
  simp[expr_body_pre_gas_obs, vv_post_initial_gas, stmt_state_rel_gas_obs,
       literal_ptr_ghost_kept_initial_gas, ifexp_expr_post_initial_gas] >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Theorem ifexp_selected_nonword_marked:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty c a b) es_outer /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  ~is_word_type ty /\ ~ce.ce_is_ctor /\
  compile_expr ce rty arm sa = (vv,sm) /\
  compile_ifexp_arm ce ty (lowered_value_type ce arm) vv sm = (op,sd) /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_expr cx arm) (es,s0,G0,tn0)
    marks (INL raw) ee G tn (OK s) /\
  gas_admissible (bind (eval_expr cx arm) (conditional_result cx)) expr_vv_res_ok es /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx arm es sa sm s0 (ee with gas_obs := []) raw vv s /\
  ptr_vv_ok cx (expr_type arm) raw vv (ee with gas_obs := []) G tn s /\
  (!tag src. vv = StackValue tag src /\ ~is_word_type (expr_type arm) ==>
    ptr_buf_ok ce arm src G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce arm p.ptr_operand G s) /\
  ghost_inv d ce cx (ee with gas_obs := []) G tn s /\
  ghost_kept ce es sa G0 tn0 s0 G tn /\ local_ptrs_reserved ce sa /\
  fn_has_code sm sd fn /\ fn_inst_ids_distinct fn /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v tv u H tt.
    gas_marked_exec_ptr D (ctx,fn) PG
      (bind (eval_expr cx arm) (conditional_result cx)) (es,s0,G0,tn0)
      marks (INL tv) ee H tt (OK u) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx fn ce cx arm es sa sd s0 (ee with gas_obs := []) v op u /\
    ptr_val_ok cx ty v op H tt u /\ ptr_buf_ok ce (IfExp ty c a b) op H u /\
    ghost_inv d ce cx (ee with gas_obs := []) H tt u /\
    ghost_kept ce es sa G0 tn0 s0 H tt /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ifexp_raw_marked_nonword_suffix >> strip_tac >>
  drule_all ifexp_marked_conditional_source >> strip_tac >>
  drule_all ifexp_raw_marked_word_then >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
