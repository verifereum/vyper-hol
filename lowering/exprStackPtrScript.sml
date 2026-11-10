Theory exprStackPtr
Ancestors
  exprSimStack bodyPtrDefs fragGasPathPtr gasSummaryComposePtr
  gasOutcome gasContext gasSummary gasSummaryCompose gasExemptCert
  exprSimDefs loweringPosts exprLowering emitHelper compileEnv
  vyperInterpreter vyperState

Theorem expr_stack_outcome_ptr:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ H v ee G tn u)
    (\res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_expr cx e) (es,s0,G0,tn0)
    (\res ee G tn u. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx e es sa sb s0 ee (Value v) (StackValue t op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ H v ee G tn u)
    (\res ee gt r. expr_exit res r)
Proof
  rw[gas_outcome_ptr_def] >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_ptr_at_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `G`, `tn`, `OK u`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
          gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
              read_result_def, return_def, vv_own_def] >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                   `es_end`, `G`, `tn`, `r`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule eval_expr_force_value >>
      disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
  disj2_tac >> drule eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[]
QED

Theorem expr_vv_sim_stack_ptr:
  !d ctx PG func cenv cx ty e es.
    expr_sim_ptr d ctx PG func cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rw[expr_vv_sim_ptr_def] >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >> disch_then drule_all >> disch_tac >>
  drule_all (BETA_RULE (Q.INST [`H` |-> `\v ee G tn u.
    ghost_inv d cenv cx ee G tn u /\
    ptr_val_ok cx (expr_type e) v op G tn u /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G u) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn`] expr_stack_outcome_ptr)) >>
  disch_then (qspec_then `t` assume_tac) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[ptr_vv_ok_def, read_result_def, return_def] >>
  metis_tac[]
QED
