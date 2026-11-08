Theory entryAssignableCardinality
Ancestors
  combin list rich_list finite_map words vyperValue vyperTypeSystem vyperTypeDefaults

Theorem evaluated_assignable_members_slot_bound:
  !tys tenv tvs.
    EVERY (assignable_type tenv) tys /\
    evaluate_types tenv tys [] = SOME tvs ==>
    LENGTH tys = LENGTH tvs /\ LENGTH tvs <= type_slot_size_list tvs
Proof
  Induct >> simp[evaluate_types_OPT_MMAP, OPT_MMAP_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all assignable_type_slot_size_pos >> strip_tac >>
  first_x_assum drule >>
  simp[evaluate_types_OPT_MMAP, type_slot_size_def] >> decide_tac
QED

Theorem assignable_tuple_member_count:
  assignable_type tenv (TupleT tys) ==> LENGTH tys <= dimword (:256)
Proof
  simp[assignable_type_def, well_formed_type_def, evaluate_type_def,
       AllCaseEqs(), type_slot_size_def] >>
  rpt strip_tac >>
  Cases_on `evaluate_types tenv tys []` >>
  gvs[SF ETA_ss, AllCaseEqs()] >>
  drule_all evaluated_assignable_members_slot_bound >> strip_tac >>
  Cases_on `type_slot_size_list x <= dimword (:256)` >> gvs[]
QED

Theorem slot_size_fields_zip[local]:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_slot_size_fields (ZIP (names,tvs)) = type_slot_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_slot_size_def]
QED

Theorem assignable_struct_member_count:
  assignable_type tenv (StructT nsid) /\
  FLOOKUP tenv nsid = SOME (StructArgs fields) ==>
  LENGTH fields <= dimword (:256)
Proof
  simp[assignable_type_def, well_formed_type_def, evaluate_type_def,
       AllCaseEqs(), type_slot_size_def] >>
  rpt strip_tac >>
  `EVERY (assignable_type (tenv \\ nsid)) (MAP SND fields)` by
    fs[EVERY_MAP, o_DEF] >>
  gvs[] >>
  Cases_on `evaluate_types (tenv \\ nsid) (MAP SND fields) []` >>
  gvs[] >> rename1 `evaluate_types _ _ [] = SOME tvs` >>
  drule_all evaluated_assignable_members_slot_bound >> strip_tac >>
  gvs[] >>
  `type_slot_size_fields (ZIP (MAP FST fields,tvs)) =
   type_slot_size_list tvs` by (irule slot_size_fields_zip >> simp[]) >>
  gvs[] >> Cases_on `type_slot_size_list tvs <= dimword (:256)` >> gvs[]
QED
