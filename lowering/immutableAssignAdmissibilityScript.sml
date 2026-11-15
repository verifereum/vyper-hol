(* Successful, typed assignment values satisfy the immutable encoding shape. *)
Theory immutableAssignAdmissibility
Ancestors
  immutableEncoding immutableDeployAssignAdmissible exprSimSource vyperTypeArgFits
  vyperTypeValues vyperTyping

Theorem immutable_assignment_rhs_admissible:
  !cenv cx env e es ity dtv pv ee v.
    expr_body_pre cenv cx env e es /\
    env.type_defs = get_tenv cx /\
    type_widens_to env.type_defs (expr_type e) ity /\
    evaluate_type (get_tenv cx) ity = SOME dtv /\
    eval_expr cx e es = (INL pv,ee) /\
    read_result cx pv ee = (INL v,ee) ==>
    immutable_value_admissible dtv v
Proof
  rpt strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt v` by metis_tac[] >>
  `value_has_type dtv v` by
    metis_tac[type_widens_to_value_has_type, optionTheory.SOME_11] >>
  irule typed_immutable_admissible >>
  metis_tac[evaluate_type_well_formed_type_value]
QED
