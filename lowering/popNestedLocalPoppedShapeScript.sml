Theory popNestedLocalPoppedShape
Ancestors
  popNestedLocalPoppedPath vyperState vyperTyping vyperValueOperation
  vyperAssignPreservesType
  vyperTypeStatePreservation vyperArray

Theorem fixed_shape_path_transport:
  !path tv a b x.
    fixed_shape_path tv path /\ well_formed_type_value tv /\
    value_has_type tv a /\ value_has_type tv b /\
    evaluate_subscripts tv a path = INL x ==>
    ?y. evaluate_subscripts tv b path = INL y
Proof
  Induct_on `path`
  >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tv` >> gvs[fixed_shape_path_def, AllCaseEqs()]
  >~ [`value_has_type (ArrayTV et bd) a`]
  >- (Cases_on `bd` >> Cases_on `h` >> gvs[] >>
      Cases_on `v` >> gvs[] >>
      qmatch_goalsub_rename_tac `evaluate_subscripts _ newval _` >>
      rename1 `evaluate_subscripts _ oldval _ = INL x` >>
      Cases_on `oldval` >> Cases_on `newval` >>
      gvs[value_has_type_def] >>
      suspend "static") >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[value_has_type_def] >>
  suspend "struct"
QED

Resume fixed_shape_path_transport[static]:
  `well_formed_type_value et` by gvs[well_formed_type_value_def] >>
  `?v. array_index (ArrayTV et (Fixed n)) a' i = SOME v` by
    (Cases_on `a'` >> gvs[value_has_type_def, array_index_def] >>
     CASE_TAC >> simp[]) >>
  `value_has_type et v` by metis_tac[array_index_has_type] >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  first_x_assum irule >>
  metis_tac[array_index_has_type]
QED

Resume fixed_shape_path_transport[struct]:
  Cases_on `h` >> gvs[AllCaseEqs()] >>
  Cases_on `ALOOKUP l s` >> gvs[] >>
  rename1 `ALOOKUP l name = SOME ft` >>
  `well_formed_type_value ft` by
    (gvs[well_formed_type_value_def, listTheory.EVERY_MEM] >>
     metis_tac[alistTheory.ALOOKUP_MEM, pairTheory.SND]) >>
  `?v. ALOOKUP l'' name = SOME v` by
    (Cases_on `ALOOKUP l'' name` >>
     metis_tac[struct_has_type_alookup_none, optionTheory.NOT_SOME_NONE]) >>
  `value_has_type ft v` by metis_tac[struct_field_has_type, optionTheory.SOME_11] >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  first_x_assum irule >>
  metis_tac[struct_field_has_type, optionTheory.SOME_11]
QED

Finalise fixed_shape_path_transport
