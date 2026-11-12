Theory bodyPtrIfExpSourceTyping
Ancestors
  bodyPtrIfExpEndpointTyping bodyPtrIfExpMemoryTransport
  exprSimHyps exprSimHypsDefs memoryLocalRhsProps vyperState

Theorem ifexp_source_lowered_typed:
  !tops ctx ce cx env e es raw ee v er.
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) ==>
    ?sv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME sv /\
         value_has_type sv v
Proof
  rpt strip_tac >>
  Cases_on `?ann id args drv. e = Call ann (IntCall id) args drv`
  >- (gvs[] >> drule_all ifexp_internal_call_lowered_typed >> simp[]) >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     conj_tac >- metis_tac[] >>
     qexistsl [`cx`, `es`, `er`] >> simp[bind_def]) >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> metis_tac[]
QED
