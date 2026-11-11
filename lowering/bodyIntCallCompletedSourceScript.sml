Theory bodyIntCallCompletedSource
Ancestors
  bodyIntCallCompletedPath bodyIntCallReturnSource gasSummary exprSimDefs
  fragGasFocus fragGasMode fragExec vyperInterpreter vyperState
Libs
  monadsyntax

Theorem invoke_cleanup_abort_summary:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_marked_exec F (ctx,callee) f (es,entered) marks
    (INR ex) ee (Abort a cs) /\
  expr_exit (INR ex) (Abort a cs) ==>
  gas_summary_at F (ctx,func) marks
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od)
    (es,t) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    (drule gas_invoke_entry_readings >> simp[]) >>
  fs[gas_marked_exec_def, gas_marked_path_def] >>
  `gas_path ctx func t (LENGTH marks) (Abort a cs)` by
    (irule invoke_abort_counted_path >> goal_assum (drule_at Any) >> simp[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INR ex`,`ee with scopes := prev`,`Abort a cs`] >>
  simp[exit_result_def] >> reverse conj_tac
  >- (Cases_on `ex` >> gvs[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  disch_then (mp_tac o MATCH_MP function_cleanup_cast_raise) >> simp[]
QED

Theorem invoke_cleanup_return_summary:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_admissible
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od) expr_vv_res_ok es /\
  gas_marked_exec F (ctx,callee) f (es,entered) marks
    (INL v) ee (IntRet ir cs) /\
  gas_path ctx func t (LENGTH marks + k) (OK out) /\
  Q (INL (Value v)) ((ee with scopes := prev) with gas_obs := []) out ==>
  value_has_type rtv v /\
  gas_summary_at F (ctx,func) (marks ++ REPLICATE k F)
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
        return (Value crv) od)
    (es,t) Q R
Proof
  strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    (drule gas_invoke_entry_readings >> simp[]) >>
  fs[gas_marked_exec_def, gas_marked_path_def] >>
  `!tail. (do rv <- finally f
                 (do pop_function prev; unlock_if_nr cx F view od);
              crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
              return (Value crv) od)
      (es with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
      (INL (Value v),(ee with scopes := prev) with gas_obs := tail) /\
      value_has_type rtv v` by
    (gen_tac >> drule (SRULE [unlock_if_nr_def] function_cleanup_return_typed) >>
     disch_then (qspecl_then [`v`,`gas_explicit marks t.vs_gas_readings ++ tail`,
                              `ee with gas_obs := tail`] mp_tac) >>
     simp[unlock_if_nr_def]) >>
  conj_tac >- metis_tac[] >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INL (Value v)`,`ee with scopes := prev`,`OK out`] >>
  fs[gas_explicit_append, unlock_if_nr_def]
QED
