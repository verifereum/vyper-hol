Theory bodyPtrSubscriptSeamArrayMemoryPrepare
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimSubscriptArraySource
  exprSimSubscriptArrayFramed gasSummaryComposePtr gasSummary
  exprSimHypsDefs vyperState

Theorem array_subscript_base_sim_ptr:
  body_expr_ptr_ok cx obj /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty obj es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env obj es` by
    metis_tac[expr_body_pre_array_subscript_base] >>
  gvs[Once body_expr_ptr_ok_def] >>
  metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs]
QED

Theorem array_subscript_index_sim_ptr:
  (!s r t. eval_expr cx obj s = (INL r,t) ==> body_expr_ptr_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx obj)
    (es,s0,G0,tn0) marks (INL r) ee G tn result ==>
  expr_sim_ptr d ctx PG func cenv cx ty idx (ee with gas_obs := [])
Proof
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL r,ee with gas_obs := [])` by
    (gvs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env idx (ee with gas_obs := [])` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     qexists_tac `ann` >> simp[]) >>
  `body_expr_ptr_ok cx idx` by metis_tac[] >>
  gvs[Once body_expr_ptr_ok_def] >>
  metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs]
QED
