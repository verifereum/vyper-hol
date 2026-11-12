(* Successful, typed assignment values satisfy the immutable encoding shape. *)
Theory immutableAssignAdmissibility
Ancestors
  immutableEncoding exprSimSource vyperTypeArgFits vyperTypeValues vyperTyping

Theorem typed_immutable_admissible_mutual[local]:
  (!tv v. well_formed_type_value tv /\ value_has_type tv v ==>
    immutable_value_admissible tv v) /\
  (!tvs vs. EVERY well_formed_type_value tvs /\ values_have_types tvs vs ==>
    immutable_tuple_admissible tvs vs) /\
  (!tv n kvs. well_formed_type_value tv /\ sparse_has_type tv n kvs ==>
    EVERY (\(i,x). i < n /\ immutable_value_admissible tv x) kvs) /\
  (!tv vs. well_formed_type_value tv /\ all_have_type tv vs ==>
    EVERY (immutable_value_admissible tv) vs) /\
  (!fields vs. EVERY (well_formed_type_value o SND) fields /\
    struct_has_type fields vs ==> immutable_fields_admissible fields vs)
Proof
  ho_match_mp_tac value_has_type_ind >>
  simp[value_has_type_def, well_formed_type_value_def,
       immutable_value_admissible_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[SORTED_lt_ALL_DISTINCT]
QED

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
  irule (cj 1 typed_immutable_admissible_mutual) >>
  metis_tac[evaluate_type_well_formed_type_value]
QED
