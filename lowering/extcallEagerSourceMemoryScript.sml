(* The eager source read uses the physical lowered argument type. *)
Theory extcallEagerSourceMemory
Ancestors
  extcallLoweredTyping aggregateCountedPureFramePrep stmtReasonVvMemory
  exprSimMemDefs exprSimHyps exprSimHypsDefs loweringPosts exprLowering
  gasSummary vyperInterpreter vyperState
Libs monadsyntax

Theorem extcall_eager_marked_lowered_typed:
  expr_body_pre ce cx env e es /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL raw) mid (OK t) /\
  vv_post ctx func ce cx e es sa sb s0 (mid with gas_obs := []) raw vv t ==>
  expr_sim_inv ce cx env (mid with gas_obs := []) /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    (!v. read_result cx raw (mid with gas_obs := []) =
      (INL v,mid with gas_obs := []) ==> value_has_type tv v)
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL raw) mid (OK t)` by metis_tac[gas_marked_exec_from_mem] >>
  drule_all aggregate_body_tuple_marked_child_source >> strip_tac >> simp[] >>
  drule vv_post_read_ok >> strip_tac >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec T _ _ _ _ _ _ _`
      (mp_tac o CONJUNCT1 o REWRITE_RULE[gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `(do r <- eval_expr cx e; read_result cx r od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := [])` by simp[bind_def] >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all extcall_read_lowered_typed >> strip_tac >>
  qexists_tac `ltv` >> simp[] >> rpt strip_tac >> gvs[]
QED
