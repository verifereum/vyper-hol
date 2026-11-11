Theory bodyPtrIfExpConditionSource
Ancestors
  stmtSimIfProps exprSimWordArgs exprSimDefs loweringPosts
  vyperInterpreter vyperState gasSummaryComposePtr gasContext

(* Scope-domain preservation is already exported, in its general forced-expression
   form, by exprSimWordArgs.forced_eval_expr_preserves_scopes_dom. *)

Theorem ifexp_branch_admissible:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!tail. bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  gas_admissible
    (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  qpat_x_assum `!tail. _` (qspec_then `gs` assume_tac) >>
  gvs[bind_def, AllCaseEqs()] >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def] >>
  Cases_on `sel` >> gvs[bind_def]
QED

Theorem ifexp_condition_bool:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  ?sel. v = BoolV sel
Proof
  strip_tac >>
  Cases_on `v = BoolV T` >- metis_tac[] >>
  Cases_on `v = BoolV F` >- metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  gvs[bind_def, AllCaseEqs()] >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def,
       raise_def, expr_vv_res_ok_def]
QED
