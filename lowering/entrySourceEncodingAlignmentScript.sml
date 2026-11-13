Theory entrySourceEncodingAlignment
Ancestors
  vyperTypeABI vyperTypeDefaults vyperTyping vyperTypeSystem vyperValue
  vyperAssignPreservesType list rich_list

(* Reuse evaluate_types_LIST_REL, struct_has_type_values_have_types and
   ALOOKUP_sparse_has_type for evaluation, struct and sparse inversion. *)
Theorem evaluated_assignable_values_alignment:
  !tys tvs vs.
    EVERY (assignable_type env) tys /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    values_have_types tvs vs ==>
    LIST_REL (\ty v. assignable_type env ty /\
      ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem assignable_tuple_evaluation:
  assignable_type env (TupleT tys) /\
  evaluate_type env (TupleT tys) = SOME tv ==>
  ?tvs. tys <> [] /\ EVERY (assignable_type env) tys /\
    tv = TupleTV tvs /\ evaluate_types env tys [] = SOME tvs /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs
Proof
  simp[Once assignable_type_def, Once evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> gvs[EVERY_MEM]
QED

Theorem assignable_struct_evaluation:
  assignable_type env (StructT nsid) /\
  evaluate_type env (StructT nsid) = SOME tv ==>
  ?fields tvs. FLOOKUP env nsid = SOME (StructArgs fields) /\
    fields <> [] /\ EVERY (assignable_type (env \\ nsid) o SND) fields /\
    evaluate_types (env \\ nsid) (MAP SND fields) [] = SOME tvs /\
    tv = StructTV (ZIP (MAP FST fields,tvs)) /\
    LIST_REL (\ty tv. evaluate_type (env \\ nsid) ty = SOME tv)
      (MAP SND fields) tvs
Proof
  simp[Once assignable_type_def, Once evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule evaluate_types_LIST_REL >> gvs[EVERY_MEM]
QED
