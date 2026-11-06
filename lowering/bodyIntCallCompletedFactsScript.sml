Theory bodyIntCallCompletedFacts
Ancestors
  bodyIntCallReturnSource gasSummary exprLoweringProps vyperState vyperInterpreter
  compileEnv
Libs
  monadsyntax

Theorem marked_cleanup_return_typed:
  gas_admissible
    (do rv <- finally f (do pop_function prev; unlock_if_nr cx F view od);
        crv <- lift_option_type (safe_cast tv rv) "IntCall cast ret";
        return (Value crv) od) expr_vv_res_ok es /\
  gas_marked_exec F (ctx,callee) f (es,entered) marks (INL v) ee r ==>
  value_has_type tv v
Proof
  strip_tac >> fs[gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  drule_all (SRULE [unlock_if_nr_def] function_cleanup_return_typed) >> simp[]
QED

Theorem immutable_alloca_sep_gas_obs[simp]:
  immutable_alloca_sep func ce cx
    (es with <|scopes := prev; gas_obs := gs|>) t =
  immutable_alloca_sep func ce cx (es with scopes := prev) t
Proof
  simp[immutable_alloca_sep_def]
QED

Theorem marked_body_immutable_alloca_sep:
  gas_marked_exec F (ctx,callee)
    (try (do eval_stmts cxf ss; return NoneV od) handle_function)
    (es,entered) marks res ee r /\
  immutable_alloca_sep func ce cx (es with scopes := prev) t ==>
  immutable_alloca_sep func ce cx (ee with scopes := prev) t
Proof
  strip_tac >> fs[gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  drule function_body_immutable_alloca_sep >>
  disch_then (qspecl_then [`t`,`prev`,`func`,`cx`,`ce`] mp_tac) >>
  simp[]
QED
