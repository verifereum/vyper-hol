(* Semantic post-type widening at a return endpoint. *)
Theory bodyIntCallFamStmtReturnEndpointTypes
Ancestors
  exprSimHyps exprSimHypsDefs loweringPosts vyperTypeInvariants
  bodyIntCallJointStmtBoundary stmtSimReturnWiden
  exprSimSource exprSimDefs gasSummary vyperTypeExprSoundness
  vyperTypeArgFits valueEncodingTyping

Theorem return_post_type_widens:
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) dty ==>
  type_widens_to (get_tenv cx) (post_value_type ce e) dty
Proof
  strip_tac >>
  drule_all post_value_type_widens >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  metis_tac[type_widens_to_trans]
QED

Theorem return_stack_post_type:
  expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) dty /\
  0 < returns_stack_count sft dty ==>
  post_value_type ce e = dty
Proof
  strip_tac >> drule_all return_post_type_widens >> strip_tac >>
  drule_all stack_return_widens_eq >> simp[]
QED

Theorem marked_forced_post_typed:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s) marks (INL v) ee r ==>
  ?tv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
       value_has_type tv v
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `expr_body_pre ce cx env e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by
    simp[expr_body_pre_gas_obs] >>
  drule_all (REWRITE_RULE [ETA_THM] memory_rhs_read_post_typed) >>
  simp[value_runtime_typed_def] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_pre_def, expr_sim_inv_def,
       env_consistent_def, env_context_consistent_def] >> simp[]
QED

Theorem marked_forced_destination_typed:
  expr_body_pre ce cx env e es /\
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s) marks (INL v) ee r /\
  type_widens_to (get_tenv cx) (post_value_type ce e) dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv ==>
  value_has_type dtv v
Proof
  strip_tac >> drule_all marked_forced_post_typed >> strip_tac >>
  drule_all type_widens_to_value_has_type >> simp[]
QED
