(* Recover the actual gas-marked child input, not a second evaluation.
   This is the source boundary used before ADD/materialization in cons. *)
Theory bodyPtrMakeArrayConsSource
Ancestors
  bodyPtrDefs gasSummaryComposePtr exprSimAggregateSource exprSimSource
  exprSimMemorySource loweringPosts gasSummary vyperState

Theorem literal_vv_post_marked_input:
  vv_post ctx func ce cx e (es with gas_obs := gs) si sm s0 ee raw vv s <=>
  vv_post ctx func ce cx e es si sm s0 ee raw vv s
Proof
  simp[vv_post_def, locals_kept_def]
QED

Theorem literal_marked_child_materialises:
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx e)
    (es,s0,G0,tn0) marks (INL raw) mid G tn (OK s) /\
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  vv_post ctx func ce cx e es si sm s0 (mid with gas_obs := []) raw vv s ==>
  ?v.
    eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL raw,mid with gas_obs := []) /\
    expr_body_pre ce cx env e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) /\
    vv_post ctx func ce cx e
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
      si sm s0 (mid with gas_obs := []) raw vv s /\
    read_result cx raw (mid with gas_obs := []) =
      (INL v,mid with gas_obs := []) /\
    (!tail. read_result cx raw (mid with gas_obs := tail) =
      (INL v,mid with gas_obs := tail)) /\
    value_has_type tv v /\ val_wf tv v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL raw,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule vv_post_materialises >> strip_tac >>
  qexists `v` >> simp[literal_vv_post_marked_input] >>
  conj_tac
  >- (drule read_result_gas_obs >> simp[] >> metis_tac[]) >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  metis_tac[aggregate_materialised_child_typed, aggregate_materialised_child_wf]
QED
