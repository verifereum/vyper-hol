Theory bodyPtrPopTargetSimArrayCompose
Ancestors
  bodyPtrPopTargetSimSubscriptCuts bodyPtrPopTargetSimArrayGas
  gasSummaryComposePtr gasSummary targetPlaceSimDefs exprSimDefs
  vyperInterpreter vyperState gasContext list bodyPtrPopTargetSimBoundary
  targetPlaceSimCasesBase targetPlaceSim exprSimHypsDefs exprSimHyps bodySim

Theorem target_subscript_index_admissible_ptr:
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL pv) mid G tn (OK t) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_ptr_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >> rename1 `INR ex` >>
  `target_res_ok (INR ex : eval_result + exception)` suffices_by
    simp[target_res_ok_def, expr_res_ok_def] >>
  qpat_x_assum `!gs res ee. _ ==> _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  simp[Once evaluate_def, bind_assoc] >>
  disch_then (qspecl_then [`INR ex`, `ee`] mp_tac) >>
  gvs[bind_def, AllCaseEqs()]
QED

Theorem target_subscript_index_ready_ptr:
  body_inv tops ctx cenv cx /\
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  gas_marked_exec_ptr D (ctx,fn) PG (eval_base_place cx bt)
    (es,s0,G0,tn0) marks (INL pv) mid G tn (OK t) ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  expr_sim_ptr d ctx PG fn cenv cx ty e (mid with gas_obs := []) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  strip_tac >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL pv,mid with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (irule eval_base_place_sim_inv >>
     qexistsl_tac [`bt`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                  `INL pv`] >>
     fs[target_pre_def] >> metis_tac[target_pre_sub, target_pre_def]) >> simp[] >>
  conj_tac
  >- (irule target_index_body_sim_ptr >> fs[target_pre_def] >> metis_tac[]) >>
  drule_all target_subscript_index_admissible_ptr >> simp[]
QED
