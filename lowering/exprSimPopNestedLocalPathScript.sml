(* Typed mutable traversal: replacement and exact same-path readback. *)
Theory exprSimPopNestedLocalPath
Ancestors
  vyperState vyperValueOperation vyperTyping vyperTypeInvariants vyperAssignPreservesType
  vyperPlaceWriteSoundness vyperArray vyperPlaceResultTyping alist

Theorem assign_subscripts_replace_readback:
  !path tv a old nv.
    mutable_place_path tv path /\ value_has_type tv a /\
    well_formed_type_value tv /\ evaluate_subscripts tv a path = INL old ==>
    ?updated. assign_subscripts tv a path (Replace nv) = INL updated /\
      evaluate_subscripts tv updated path = INL nv
Proof
  Induct_on `path` >- simp[assign_subscripts_def, evaluate_subscripts_def] >>
  rpt gen_tac >> rename1 `mutable_place_path tv (sb::path)` >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      simp[mutable_place_path_def] >> strip_tac >>
      qmatch_assum_rename_tac `value_has_type (ArrayTV etv bd) a` >>
      `?arr. a = ArrayV arr` by (Cases_on `a` >> gvs[value_has_type_def]) >>
      pop_assum strip_assume_tac >> gvs[] >>
      gvs[Once evaluate_subscripts_def, AllCaseEqs()] >>
      `well_formed_type_value etv` by fs[well_formed_type_value_def] >>
      `value_has_type etv v` by
        (irule array_index_has_type >> simp[] >> goal_assum drule >> simp[]) >>
      first_x_assum drule_all >> disch_then (qspec_then `nv` strip_assume_tac) >>
      `array_is_mutable arr` by (Cases_on `arr` >> gvs[value_has_type_def]) >>
      `valid_index (ArrayTV etv bd) arr i` by
        (irule array_index_bounds >> conj_tac
         >- (Cases_on `arr` >> Cases_on `bd` >> gvs[value_has_type_def]) >>
         goal_assum drule) >>
      qexists_tac `ArrayV (array_set (ArrayTV etv bd) arr i updated)` >>
      simp[Once assign_subscripts_def, array_set_index_INL] >>
      simp[Once evaluate_subscripts_def, array_set_index_same]) >>
  Cases_on `tv` >> simp[mutable_place_path_def] >>
  qmatch_goalsub_rename_tac `ALOOKUP fields id` >>
  Cases_on `ALOOKUP fields id` >> simp[] >> strip_tac >>
  qmatch_assum_rename_tac `ALOOKUP fields id = SOME ftv` >>
  `?values. a = StructV values` by (Cases_on `a` >> gvs[value_has_type_def]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  gvs[Once evaluate_subscripts_def, AllCaseEqs()] >>
  `well_formed_type_value ftv` by
    (drule_all well_formed_struct_field_type >> simp[]) >>
  `value_has_type ftv v` by
    (fs[value_has_type_def] >> drule_all struct_field_has_type >> simp[]) >>
  first_x_assum drule_all >> disch_then (qspec_then `nv` strip_assume_tac) >>
  qexists_tac `StructV (AFUPDKEY id (K updated) values)` >>
  simp[Once assign_subscripts_def] >>
  simp[Once evaluate_subscripts_def, AFUPDKEY_ALOOKUP]
QED

Theorem assign_subscripts_shorten_readback:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
  subscripts_type tv path = SOME (ArrayTV etv (Dynamic n)) /\ vs <> [] ==>
  ?updated.
    assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) =
      INL updated /\
    evaluate_subscripts tv updated path = INL (ArrayV (DynArrayV (FRONT vs))) /\
    evaluate_subscripts tv updated
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) =
      INR (RuntimeError "evaluate_subscripts array_index")
Proof
  strip_tac >> drule_all assign_subscripts_replace_readback >>
  disch_then (qspec_then `ArrayV (DynArrayV (FRONT vs))` strip_assume_tac) >>
  qexists_tac `updated` >> simp[] >>
  drule_all evaluate_subscripts_append >> disch_then (qspec_then
    `[ValueSubscript (IntV &(LENGTH vs - 1))]` SUBST1_TAC) >>
  simp[evaluate_subscripts_def, array_index_def, listTheory.oEL_THM,
       rich_listTheory.LENGTH_FRONT]
QED
