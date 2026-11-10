(* Typed integer inversion at the actual source input of a marked path. *)
Theory bodyIntCallFamStmtForCheckedEndpoint
Ancestors
  bodySimDeclCases exprSimSource gasSummary

Theorem marked_forced_integer_typed:
  expr_body_pre ce cx env e es /\ is_int_type typ /\
  expr_type e = typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s) marks (INL v) ee r ==>
  ?n. v = IntV n /\ value_has_type tyv (IntV n)
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `expr_body_pre ce cx env e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by
    simp[expr_body_pre_gas_obs] >>
  metis_tac[SIMP_RULE std_ss [pairTheory.FORALL_PROD]
    (CONV_RULE (RAND_CONV (REWR_CONV (GSYM ETA_AX)))
      body_range_endpoint_read)]
QED
