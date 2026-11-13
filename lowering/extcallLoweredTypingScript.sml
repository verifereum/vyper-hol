(* Physical layout typing at a successful immediate expression read. *)
Theory extcallLoweredTyping
Ancestors
  exprSimHyps exprSimHypsDefs exprLowering vyperTypeExprSoundness
  vyperTypeInvariants
Libs
  monadsyntax

Theorem extcall_read_lowered_typed:
  !ce cx env e es v es'.
    expr_body_pre ce cx env e es /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
    ?ltv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
      value_has_type ltv v
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?a f args d. e = Call a (IntCall f) args d`
  >- (gvs[] >> metis_tac[ifexp_intcall_read_physical_typed]) >>
  `!a f args d. e = Call a (IntCall f) args d ==>
     lowered_value_type ce e = expr_type e` by metis_tac[] >>
  drule_all memory_rhs_read_lowered_typed_unwidened >>
  strip_tac >>
  gvs[value_runtime_typed_def, expr_body_pre_def, expr_sim_inv_def,
      env_consistent_def, env_context_consistent_def]
QED
