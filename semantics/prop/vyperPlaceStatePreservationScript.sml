Theory vyperPlaceStatePreservation
Ancestors
  list rich_list option alist vyperValue vyperTyping vyperState
  vyperTypeStatePreservation

Theorem subscripts_type_append:
  !xs tv ys.
    subscripts_type tv (xs ++ ys) =
    OPTION_BIND (subscripts_type tv xs) (\mid. subscripts_type mid ys)
Proof
  Induct >> simp[subscripts_type_def] >>
  rpt gen_tac >> Cases_on `subscript_type tv h` >> simp[subscripts_type_def]
QED

Theorem subscript_type_well_formed:
  !tv sb ptv. well_formed_type_value tv /\
    subscript_type tv sb = SOME ptv ==> well_formed_type_value ptv
Proof
  Cases >> Cases >> simp[subscript_type_def] >> rpt gen_tac >>
  TRY (rename1 `ValueSubscript v` >> Cases_on `v` >> simp[subscript_type_def]) >>
  rw[subscript_type_def, well_formed_type_value_def] >>
  gvs[EVERY_MEM] >- (first_x_assum irule >> simp[MEM_EL] >> qexists_tac `Num i` >> simp[]) >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  first_x_assum (qspec_then `(s,ptv)` mp_tac) >> simp[]
QED

Theorem subscripts_type_well_formed:
  !path tv ptv. well_formed_type_value tv /\
    subscripts_type tv path = SOME ptv ==> well_formed_type_value ptv
Proof
  Induct >> simp[subscripts_type_def] >> rpt gen_tac >>
  Cases_on `subscript_type tv h` >> simp[] >>
  metis_tac[subscript_type_well_formed]
QED

Theorem tuple_index_type[local]:
  !tvs vs j v. values_have_types tvs vs /\ oEL j vs = SOME v /\
    j < LENGTH tvs ==> value_has_type (EL j tvs) v
Proof
  Induct >> Cases_on `vs` >> simp[value_has_type_def] >>
  Cases_on `j` >> simp[oEL_def, value_has_type_def] >>
  metis_tac[]
QED

Theorem array_index_type_metadata[local]:
  !tv mtv av i etv v.
    (mtv = tv \/ mtv = NoneTV) /\ value_has_type tv (ArrayV av) /\
    well_formed_type_value tv /\
    subscript_type tv (ValueSubscript (IntV i)) = SOME etv /\
    array_index mtv av i = SOME v ==> value_has_type etv v
Proof
  Cases >> simp[subscript_type_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >> Cases_on `av` >>
  gvs[value_has_type_def, subscript_type_def, well_formed_type_value_def,
      vyperValueOperationTheory.array_index_def, AllCaseEqs()] >>
  TRY (irule tuple_index_type >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  TRY (rename1 `value_has_type (ArrayTV t bd) _` >> Cases_on `bd` >>
       gvs[value_has_type_def]) >>
  metis_tac[tuple_index_type, vyperAssignPreservesTypeTheory.oEL_all_have_type,
    vyperAssignPreservesTypeTheory.ALOOKUP_sparse_has_type,
    default_value_well_typed]
QED

Theorem evaluate_subscripts_type_metadata:
  !path tv mtv a ptv v.
    (mtv = tv \/ mtv = NoneTV) /\
    value_has_type tv a /\ well_formed_type_value tv /\
    subscripts_type tv path = SOME ptv /\
    evaluate_subscripts mtv a path = INL v ==> value_has_type ptv v
Proof
  Induct >> simp[subscripts_type_def, evaluate_subscripts_def] >>
  gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> rpt gen_tac >> strip_tac >>
      gvs[subscripts_type_def, AllCaseEqs(), evaluate_subscripts_def] >>
      `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
      `value_has_type etv v'` by metis_tac[array_index_type_metadata] >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> Cases_on `mtv` >> gvs[subscript_type_def]) >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  rename1 `subscript_type root_tv (AttrSubscript s) = SOME etv` >>
  Cases_on `root_tv` >> gvs[subscript_type_def] >>
  Cases_on `a` >> gvs[value_has_type_def, evaluate_subscripts_def, AllCaseEqs()] >>
  `well_formed_type_value etv` by
    metis_tac[subscript_type_well_formed, subscript_type_def] >>
  `value_has_type etv v'` by
    (drule vyperAssignPreservesTypeTheory.struct_field_has_type >>
     disch_then drule >> strip_tac >> gvs[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem evaluate_subscripts_type:
  !path tv a ptv v.
    value_has_type tv a /\ well_formed_type_value tv /\
    subscripts_type tv path = SOME ptv /\
    evaluate_subscripts tv a path = INL v ==> value_has_type ptv v
Proof
  metis_tac[evaluate_subscripts_type_metadata]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place boundary: " ^ name ^ "\n")
     else raise Fail ("Incomplete place boundary: " ^ name)
  end) (DB.thms "vyperPlaceStatePreservation");
