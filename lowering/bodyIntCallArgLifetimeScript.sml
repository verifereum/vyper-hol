(* Deferred internal-call argument interface probes. *)
Theory bodyIntCallArgLifetime
Ancestors
  exprSimAggregateChildren exprSimAggregateSource exprLowering compileEnv vyperEvalPureExpr vyperPureExpr supportedExprs supportedExprForms

Theorem compile_multi_vvs_empty:
  compile_multi_vvs cfn cenv [] st = ([],st)
Proof
  simp[compile_multi_vvs_def, comp_return_def]
QED

Theorem compile_stage_intcall_args_empty:
  compile_stage_intcall_args cenv [] flags tys st = ([],st)
Proof
  simp[compile_stage_intcall_args_def, comp_return_def]
QED

Theorem supported_purity_semantic:
  (!tops e. supported_pure_expr tops e ==> pure_expr e) /\
  (!tops es. supported_pure_exprs tops es ==> EVERY pure_expr es) /\
  (!tops fields. supported_pure_fields tops fields ==>
     EVERY pure_expr (MAP SND fields)) /\
  (!tops e. supported_place_expr tops e ==> pure_expr e)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def, pure_expr_def, SF ETA_ss] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `es` >> simp[supported_builtin_form_def]
QED

Theorem supported_pure_eval_expr_state:
  supported_pure_expr tops e /\ eval_expr cx e es = (res,es') ==>
  es' = es
Proof
  metis_tac[supported_purity_semantic, eval_expr_preserves_state]
QED
