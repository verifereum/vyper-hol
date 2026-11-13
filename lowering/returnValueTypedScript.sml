(* A returned value's source evaluation: the counted summary's marked run
   gives it, and with the source typing it gives the value's runtime type. *)
Theory returnValueTyped
Ancestors
  exprSimHypsDefs vyperTypeEvalSoundness vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeInvariants gasSummary

Theorem marked_exec_source_eq:
  gas_marked_exec m p source (es, s0) marks res es_end r ==>
  ?g es'. source (es with gas_obs := g) = (res, es')
Proof
  PairCases_on `p` >> rw[gas_marked_exec_def] >> metis_tac[]
QED

Theorem return_value_typed:
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) =
    (INL v, es') ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       value_has_type tv v
Proof
  rw[expr_sim_inv_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
  `call_evaluation_safe cx (int_calls_expr e)`
    by gvs[int_calls_stmt_def, int_calls_expr_def] >>
  mp_tac (Q.INST [`st` |-> `es with gas_obs := g`, `res` |-> `INL v`,
                  `st'` |-> `es'`] eval_expr_read_type_sound) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  gvs[value_runtime_typed_def, env_consistent_def,
      env_context_consistent_def]
QED
