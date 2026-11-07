(* Evaluated type validity and source typing imply immutable admissibility. *)
Theory immutableDeployAssignAdmissible
Ancestors
  immutableEncoding vyperTyping vyperTypeValues list relation sorting

Theorem typed_immutable_admissible_mutual[local]:
  (!tv v. well_formed_type_value tv /\ value_has_type tv v ==>
    immutable_value_admissible tv v) /\
  (!tvs vs. EVERY well_formed_type_value tvs /\ values_have_types tvs vs ==>
    immutable_tuple_admissible tvs vs) /\
  (!tv n sparse. well_formed_type_value tv /\ sparse_has_type tv n sparse ==>
    EVERY (\(i,v). i < n /\ immutable_value_admissible tv v) sparse) /\
  (!tv vs. well_formed_type_value tv /\ all_have_type tv vs ==>
    EVERY (immutable_value_admissible tv) vs) /\
  (!ftypes fields. EVERY (well_formed_type_value o SND) ftypes /\
    struct_has_type ftypes fields ==> immutable_fields_admissible ftypes fields)
Proof
  ho_match_mp_tac value_has_type_ind >>
  rw[value_has_type_def, immutable_value_admissible_def,
     well_formed_type_value_def] >>
  gvs[SF ETA_ss] >> metis_tac[SORTED_lt_ALL_DISTINCT]
QED

Theorem typed_immutable_admissible:
  well_formed_type_value tv /\ value_has_type tv v ==>
  immutable_value_admissible tv v
Proof
  metis_tac[typed_immutable_admissible_mutual]
QED

Theorem default_immutable_admissible:
  well_formed_type_value tv ==>
  immutable_value_admissible tv (default_value tv)
Proof
  metis_tac[typed_immutable_admissible, default_value_well_typed]
QED

Theorem evaluated_immutable_admissible:
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  immutable_value_admissible tv v
Proof
  metis_tac[typed_immutable_admissible, evaluate_type_well_formed_type_value]
QED
