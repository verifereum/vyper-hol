(* Raw singleton capture, before delayed materialization. *)
Theory createCtorTupleCaptureSource
Ancestors
  exprSimDefs exprSimAggregateBodySource vyperInterpreter vyperState

Theorem ctor_capture_singleton_raw_outcome:
  expr_vv_sim ctx func ce cx ty e es /\
  compile_expr ce ty e c1 = (vv,c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_expr_results cx [e]) (es,s_buf)
    (\H res ee t. ?raw. res = INL [raw] /\
      vv_post H ctx func ce cx e es c1 c_vvs s_buf ee raw vv t /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (?gs. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee)))
    (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `eval_expr_results cx [e] =
    bind (eval_expr cx e) (return o (\raw. [raw]))` by
    simp[evaluate_def, bind_return, combinTheory.o_DEF] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`st0`, `c1`, `c_vvs`, `vv`, `s_buf`] mp_tac) >>
  simp[] >> strip_tac >>
  irule gas_outcome_map_source_run >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt gen_tac >>
      `expr_exit (SUM_MAP (\raw. [raw]) I res) = expr_exit res` by
        (simp[sumTheory.SUM_MAP_CASE, combinTheory.o_DEF] >>
         metis_tac[expr_exit_success_map]) >>
      simp[] >> Cases_on `res` >> simp[halt_exit_def]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
