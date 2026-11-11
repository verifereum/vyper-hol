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

(* Popping a dynamic array kills no live path inside it and revives no dead
   one: a path dead in the array is dead in the array without its last
   element. *)
Theorem evaluate_subscripts_front_dead:
  !k tv vs e.
    vs <> [] /\ evaluate_subscripts tv (ArrayV (DynArrayV vs)) k = INR e ==>
    ?e'. evaluate_subscripts tv (ArrayV (DynArrayV (FRONT vs))) k = INR e'
Proof
  Cases >- simp[evaluate_subscripts_def] >>
  rename1 `sb::k` >> rpt gen_tac >>
  Cases_on `sb` >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  simp[evaluate_subscripts_def] >>
  rename1 `IntV i` >>
  simp[array_index_def] >> Cases_on `0 <= i` >> simp[] >>
  Cases_on `Num i < LENGTH vs - 1` >>
  gvs[listTheory.oEL_THM, rich_listTheory.LENGTH_FRONT] >>
  strip_tac >>
  `EL (Num i) (FRONT vs) = EL (Num i) vs` by
    (irule rich_listTheory.EL_FRONT >>
     gvs[listTheory.NULL_EQ, rich_listTheory.LENGTH_FRONT]) >>
  `Num i < LENGTH vs` by decide_tac >>
  gvs[AllCaseEqs()]
QED

(* Replacing the value at a live path by one with no more live paths keeps
   every dead path of the whole value dead. *)
Theorem assign_subscripts_replace_dead:
  !path tv a old nv updated k e.
    evaluate_subscripts tv a path = INL old /\
    (!tv' k e. evaluate_subscripts tv' old k = INR e ==>
               ?e'. evaluate_subscripts tv' nv k = INR e') /\
    assign_subscripts tv a path (Replace nv) = INL updated /\
    evaluate_subscripts tv a k = INR e ==>
    ?e'. evaluate_subscripts tv updated k = INR e'
Proof
  Induct
  >- (simp[evaluate_subscripts_def, assign_subscripts_def] >> metis_tac[]) >>
  qx_gen_tac `sb` >> rpt gen_tac >>
  Cases_on `k` >- simp[evaluate_subscripts_def] >>
  rename1 `evaluate_subscripts _ _ (sb'::kt) = INR _` >>
  Cases_on `sb` >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  simp[evaluate_subscripts_def, assign_subscripts_def]
  >- (rename1 `IntV i` >> Cases_on `a` >>
      simp[evaluate_subscripts_def, assign_subscripts_def] >>
      rename1 `ArrayV av` >> strip_tac >> gvs[AllCaseEqs()] >>
      `?av'. updated = ArrayV av'` by
        (qpat_x_assum `array_set_index _ _ _ _ = _` mp_tac >>
         simp[array_set_index_def, AllCaseEqs()] >> rw[] >> simp[]) >>
      gvs[] >>
      Cases_on `sb'` >> TRY (rename1 `ValueSubscript y` >> Cases_on `y`) >>
      gvs[evaluate_subscripts_def] >>
      rename1 `ValueSubscript (IntV j)` >>
      Cases_on `j = i`
      >- (gvs[] >> drule array_index_after_set_same >> strip_tac >>
          gvs[AllCaseEqs()] >>
          first_x_assum drule >> disch_then drule >>
          disch_then drule >> disch_then drule >> strip_tac >> simp[]) >>
      `array_index tv av' j = array_index tv av j` by
        metis_tac[array_index_after_set_other] >>
      gvs[AllCaseEqs()]) >>
  rename1 `AttrSubscript id` >> Cases_on `a` >>
  simp[evaluate_subscripts_def, assign_subscripts_def] >>
  rename1 `StructV al` >> strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `sb'` >> TRY (rename1 `ValueSubscript y` >> Cases_on `y`) >>
  gvs[evaluate_subscripts_def, AFUPDKEY_ALOOKUP] >>
  rename1 `ALOOKUP al fld` >>
  Cases_on `fld = id` >> gvs[]
  >- (gvs[AllCaseEqs()] >>
      first_x_assum drule >> disch_then drule >>
      disch_then drule >> disch_then drule >> strip_tac >> simp[]) >>
  Cases_on `ALOOKUP al fld` >> gvs[AllCaseEqs()]
QED

Theorem evaluate_subscripts_append_err:
  !path tv a err sfx.
    evaluate_subscripts tv a path = INR err ==>
    evaluate_subscripts tv a (path ++ sfx) = INR err
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  Cases >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  rpt gen_tac >>
  Cases_on `a` >>
  simp[evaluate_subscripts_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> res_tac >> simp[]
QED

(* A replacement that succeeds is read back at its path. *)
Theorem assign_subscripts_replace_read:
  !path tv a nv u.
    assign_subscripts tv a path (Replace nv) = INL u ==>
    evaluate_subscripts tv u path = INL nv
Proof
  Induct >- simp[assign_subscripts_def, evaluate_subscripts_def] >>
  rpt gen_tac >>
  Cases_on `h` >> TRY (rename1 `ValueSubscript x` >> Cases_on `x`) >>
  Cases_on `a` >> simp[assign_subscripts_def] >> strip_tac >>
  gvs[AllCaseEqs()]
  >- (rename1 `array_set_index tv av i vj = INL u` >>
      `?av'. u = ArrayV av'` by
        (qpat_x_assum `array_set_index _ _ _ _ = _` mp_tac >>
         simp[array_set_index_def, AllCaseEqs()] >> rw[] >> simp[]) >>
      gvs[] >> drule array_index_after_set_same >> strip_tac >>
      simp[evaluate_subscripts_def] >> res_tac >> simp[]) >>
  simp[evaluate_subscripts_def, AFUPDKEY_ALOOKUP] >> res_tac >> simp[]
QED
