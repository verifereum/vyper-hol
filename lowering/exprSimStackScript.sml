(* Stack results retain the raw-expression counted judgment. *)
Theory exprSimStack
Ancestors
  exprSimDefs loweringPosts gasOutcome gasContext gasSummary gasSummaryCompose
  gasExemptCert fragExec exprLowering emitHelper compileEnv vyperInterpreter vyperState

Theorem eval_expr_force_value:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
  !s res ee. bind (eval_expr cx e) (read_result cx) s = (res,ee) ==>
    eval_expr cx e s =
      ((case res of INL v => INL (Value v) | INR ex => INR ex),ee)
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `eval_expr cx e s` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw`
  >- (rename1 `eval_expr cx e s = (INL tv,st)` >>
      `?v. tv = Value v` by metis_tac[] >> gvs[] >>
      simp[bind_def, read_result_def, return_def] >> strip_tac >> gvs[]) >>
  simp[bind_def] >> strip_tac >> gvs[]
QED


Theorem eval_expr_force_ignore:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
  ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()) =
  ignore_bind (eval_expr cx e) (return ())
Proof
  strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `s` >>
  Cases_on `eval_expr cx e s` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[ignore_bind_def, bind_def] >>
  rename1 `eval_expr cx e s = (INL tv,st)` >>
  `?v. tv = Value v` by metis_tac[] >> gvs[] >>
  simp[read_result_def, return_def]
QED

Theorem eval_expr_force_admissible:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  drule_all eval_expr_force_value >> strip_tac >>
  first_x_assum drule >>
  Cases_on `res` >> simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem expr_stack_outcome:
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue t op) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  rw[gas_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >>
      gvs[gas_summary_at_def, gas_marked_exec_def]
      >- (qexistsl_tac [`INL (Value v)`, `es_end`, `OK u`] >>
          simp[] >> conj_tac
          >- (gen_tac >> drule eval_expr_force_value >>
              disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
          gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
              read_result_def, return_def] >> first_assum ACCEPT_TAC) >>
      qexistsl_tac [`case res of INL v => INL (Value v) | INR ex => INR ex`,
                   `es_end`, `r`] >>
      simp[expr_exit_success_map] >> gen_tac >>
      drule eval_expr_force_value >> disch_then (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` mp_tac) >> simp[]) >>
  disj2_tac >> drule eval_expr_force_ignore >>
  disch_then (fn th => fs[th]) >> metis_tac[]
QED

Theorem expr_vv_sim_stack:
  !ctx func cenv cx ty e es.
    expr_sim ctx func cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim ctx func cenv cx ty e es
Proof
  rw[expr_vv_sim_def] >>
  first_x_assum (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op, sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  irule expr_stack_outcome >> conj_tac
  >- (first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[eval_expr_force_admissible] >>
  gvs[expr_sim_def] >> first_x_assum irule >> simp[]
QED

