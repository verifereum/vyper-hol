(* Source typing is separate from pointer representation and its ghost. *)
Theory bodyPtrMakeArrayScalarSource
Ancestors
  exprSimSource exprSimDefs vyperTyping vyperInterpreter
  vyperTypeExprResult vyperTypeInvariants exprSimHypsDefs vyperTypeExprSoundness
  context vyperState

Theorem scalar_source_result_typed:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tv,es') /\
  read_result cx tv es' = (INL v,es') ==>
  ?ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
       value_has_type ty v
Proof
  strip_tac >>
  `(do result <- eval_expr cx e; read_result cx result od) es = (INL v,es')`
    by simp[bind_def] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
QED
