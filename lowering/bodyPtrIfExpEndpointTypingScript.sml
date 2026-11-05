Theory bodyPtrIfExpEndpointTyping
Ancestors
  exprSimHyps exprSimHypsDefs memoryLocalRhsProps vyperState

Theorem ifexp_abi_encode_lowered_typed:
  !cx ce env ann ensure mid target args es raw ee v er.
    expr_body_pre ce cx env
      (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
    eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args) es = (INL raw,ee) /\
    read_result cx raw ee = (INL v,er) ==>
    ?sv. evaluate_type (get_tenv cx)
      (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) = SOME sv /\
      value_has_type sv v
Proof
  rpt strip_tac >>
  `value_runtime_typed env
     (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) v` by
    (irule memory_rhs_read_lowered_typed_unwidened >>
     conj_tac >- simp[] >>
     qexistsl [`cx`, `es`, `er`] >> simp[bind_def]) >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> metis_tac[]
QED
