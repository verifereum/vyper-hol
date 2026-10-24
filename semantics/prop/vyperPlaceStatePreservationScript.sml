Theory vyperPlaceStatePreservation
Ancestors
  list rich_list option alist vyperValue vyperTyping vyperState
  vyperTypeStatePreservation vyperPlaceInvariants

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

Theorem array_index_type_metadata:
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
      goal_assum (drule_at Any) >> simp[subscript_type_def] >>
      Cases_on `mtv` >> gvs[subscript_type_def]) >>
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

Theorem evaluate_subscripts_cons_typed:
  subscript_type tv sb = SOME etv ==>
  evaluate_subscripts tv a (sb::rest) =
    (case evaluate_subscripts tv a [sb] of
     | INL v => evaluate_subscripts etv v rest
     | INR err => INR err)
Proof
  strip_tac >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
       gvs[subscript_type_def]) >>
  Cases_on `tv` >> gvs[subscript_type_def] >>
  Cases_on `a` >>
  simp[evaluate_subscripts_def, subscript_type_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem typed_traversal_failure_is_dynamic_absence:
  !path tv a ptv err.
    value_has_type tv a /\ well_formed_type_value tv /\
    subscripts_type tv path = SOME ptv /\
    evaluate_subscripts tv a path = INR err ==>
    missing_dynamic_element tv a path
Proof
  Induct >> simp[evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`,`a`] assume_tac) >>
  Cases_on `evaluate_subscripts tv a [h]`
  >- (gvs[missing_dynamic_element_def] >>
      `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
      `subscripts_type tv [h] = SOME etv` by simp[subscripts_type_def] >>
      `value_has_type etv x` by metis_tac[evaluate_subscripts_type] >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[missing_dynamic_element_def] >>
  Cases_on `h` >>
  TRY (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
       gvs[subscript_type_def]) >>
  Cases_on `tv` >> gvs[subscript_type_def] >>
  Cases_on `a` >>
  gvs[value_has_type_def, evaluate_subscripts_def, AllCaseEqs(),
      vyperValueOperationTheory.array_index_def]
  >- (drule vyperTypingTheory.values_have_types_length >>
      gvs[oEL_THM])
  >- (Cases_on `b` >> gvs[value_has_type_def, oEL_THM]) >>
  drule struct_has_type_map_fst >>
  gvs[alistTheory.ALOOKUP_NONE] >>
  metis_tac[alistTheory.ALOOKUP_MEM, MEM_MAP, pairTheory.FST]
QED

Theorem oEL_some_bound[local]:
  !ls j v. oEL j ls = SOME v ==> j < LENGTH ls
Proof
  Induct >> Cases_on `j` >> simp[oEL_def]
QED

Theorem sparse_lookup_bound[local]:
  !ls etv n j v. sparse_has_type etv n ls /\ ALOOKUP ls j = SOME v ==> j < n
Proof
  Induct >> simp[value_has_type_def] >> gen_tac >> PairCases_on `h` >>
  rw[value_has_type_def, alistTheory.ALOOKUP_def] >> gvs[] >> metis_tac[]
QED

Theorem values_have_types_length[local]:
  !ts vs. values_have_types ts vs ==> LENGTH ts = LENGTH vs
Proof
  Induct >> Cases_on `vs` >> simp[value_has_type_def]
QED

Theorem array_index_declared_type_exists:
  !tv mtv av i v.
  (mtv = tv \/ mtv = NoneTV) /\ value_has_type tv (ArrayV av) /\
  well_formed_type_value tv /\ array_index mtv av i = SOME v ==>
  ?etv. subscript_type tv (ValueSubscript (IntV i)) = SOME etv
Proof
  Cases >> Cases_on `av` >>
  simp[value_has_type_def] >> rpt gen_tac >> strip_tac >>
  gvs[vyperValueOperationTheory.array_index_def, AllCaseEqs(), subscript_type_def] >>
  TRY (Cases_on `b` >> gvs[value_has_type_def, subscript_type_def,
       vyperValueOperationTheory.array_index_def, AllCaseEqs()]) >>
  imp_res_tac oEL_some_bound >> imp_res_tac values_have_types_length >>
  imp_res_tac sparse_lookup_bound >> gvs[value_has_type_def] >> decide_tac
QED

Theorem evaluate_subscripts_declared_type_exists:
  !path tv mtv a v.
    (mtv = tv \/ mtv = NoneTV) /\ value_has_type tv a /\
    well_formed_type_value tv /\ evaluate_subscripts mtv a path = INL v ==>
    ?ptv. subscripts_type tv path = SOME ptv /\
          well_formed_type_value ptv /\ value_has_type ptv v
Proof
  Induct >> simp[subscripts_type_def, evaluate_subscripts_def] >>
  gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> rpt gen_tac >> strip_tac >>
      gvs[evaluate_subscripts_def, AllCaseEqs()] >>
      rename1 `value_has_type root_tv (ArrayV av)` >>
      `?etv. subscript_type root_tv (ValueSubscript (IntV i)) = SOME etv` by
        metis_tac[array_index_declared_type_exists] >>
      `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
      `value_has_type etv v'` by metis_tac[array_index_type_metadata] >>
      Cases_on `root_tv` >> gvs[subscript_type_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  rename1 `value_has_type root_tv a` >>
  Cases_on `a` >> gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  Cases_on `root_tv` >> gvs[value_has_type_def] >>
  drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >> strip_tac >>
  rename1 `value_has_type field_tv field_v` >>
  `well_formed_type_value field_tv` by
    (irule subscript_type_well_formed >>
     qexistsl_tac [`AttrSubscript s`, `StructTV l'`] >> simp[subscript_type_def]) >>
  gvs[subscript_type_def] >> metis_tac[]
QED

Theorem read_popped_type:
  !history tv path ptv v.
    popped_history_typed tv history /\
    subscripts_type tv path = SOME ptv /\
    read_popped tv path history = SOME v ==> value_has_type ptv v
Proof
  Induct >> simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[popped_history_typed_cons, read_popped_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  TRY (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  `path = h0 ++ DROP (LENGTH h0) path` by
    (gvs[IS_PREFIX_APPEND] >> simp[DROP_LENGTH_APPEND]) >>
  `subscripts_type ptv' (DROP (LENGTH h0) path) = SOME ptv` by
    (qpat_x_assum `subscripts_type tv path = SOME ptv` mp_tac >>
     once_asm_rewrite_tac[] >> simp[subscripts_type_append, DROP_LENGTH_APPEND]) >>
  metis_tac[evaluate_subscripts_type]
QED

Theorem record_pop_history_typed_at_path:
  popped_history_typed tv history /\
  subscripts_type tv path = SOME (ArrayTV etv (Dynamic n)) /\
  well_formed_type_value etv /\
  value_has_type (ArrayTV etv (Dynamic n)) arr /\
  popped_value arr = INL p ==>
  popped_history_typed tv (record_pop path arr p history)
Proof
  strip_tac >>
  `value_has_type etv p` by
    metis_tac[vyperTypeStatePreservationTheory.popped_value_well_typed] >>
  Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  Cases_on `a` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  gvs[record_pop_def, popped_history_typed_cons, value_has_type_def] >>
  qexists_tac `etv` >>
  simp[subscripts_type_append, subscripts_type_def, subscript_type_def,
       vyperASTTheory.bound_length_def] >>
  `0 < n` by (Cases_on `l` >> gvs[] >> decide_tac) >> simp[]
QED

Theorem array_set_index_type_metadata[local]:
  !tv mtv av i etv v r.
    (mtv = tv \/ mtv = NoneTV) /\ value_has_type tv (ArrayV av) /\
    subscript_type tv (ValueSubscript (IntV i)) = SOME etv /\
    value_has_type etv v /\ array_set_index mtv av i v = INL r ==>
    value_has_type tv r
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (Cases_on `mtv` >> gvs[subscript_type_def] >>
      TRY (Cases_on `av` >>
           gvs[value_has_type_def, vyperValueOperationTheory.array_set_index_def,
               AllCaseEqs()] >> NO_TAC) >>
      irule vyperAssignPreservesTypeTheory.array_set_index_preserves_type >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `tv` >> Cases_on `av` >>
  gvs[subscript_type_def, value_has_type_def,
      vyperValueOperationTheory.array_set_index_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[value_has_type_def] >>
  irule vyperAssignPreservesTypeTheory.TAKE_DROP_all_have_type >> simp[]
QED

Theorem assign_subscripts_replace_type_metadata:
  !path tv mtv a ptv v new.
    (mtv = tv \/ mtv = NoneTV) /\ value_has_type tv a /\
    well_formed_type_value tv /\ subscripts_type tv path = SOME ptv /\
    value_has_type ptv v /\ assign_subscripts mtv a path (Replace v) = INL new ==>
    value_has_type tv new
Proof
  Induct >> simp[subscripts_type_def, Once assign_subscripts_def] >>
  gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[subscripts_type_def, Once assign_subscripts_def] >>
      rpt gen_tac >> strip_tac >>
      gvs[subscripts_type_def, AllCaseEqs()] >>
      rename1 `subscript_type root_tv (ValueSubscript (IntV i)) = SOME etv` >>
      `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
      `value_has_type etv v'` by metis_tac[array_index_type_metadata] >>
      `value_has_type etv vj` by
        (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
         qmatch_asmsub_abbrev_tac `assign_subscripts child_mtv _ _ _` >>
         qexistsl_tac [`v'`, `child_mtv`, `v`] >> simp[] >>
         Cases_on `root_tv` >> gvs[subscript_type_def, Abbr `child_mtv`]) >>
      irule array_set_index_type_metadata >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  rename1 `subscript_type root_tv (AttrSubscript fld) = SOME etv` >>
  Cases_on `root_tv` >> gvs[subscript_type_def] >>
  Cases_on `a` >>
  gvs[value_has_type_def, Once assign_subscripts_def, AllCaseEqs()] >>
  rename1 `assign_subscripts _ fv path (Replace v) = INL new_fv` >>
  `well_formed_type_value etv` by
    metis_tac[subscript_type_well_formed, subscript_type_def] >>
  `value_has_type etv fv` by
    (drule vyperAssignPreservesTypeTheory.struct_field_has_type >>
     disch_then drule >> strip_tac >> gvs[]) >>
  `value_has_type etv new_fv` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  irule vyperAssignPreservesTypeTheory.AFUPDKEY_struct_has_type >> simp[] >>
  qexists_tac `etv` >> rpt strip_tac >>
  drule_all vyperAssignPreservesTypeTheory.struct_field_has_type >> strip_tac >> gvs[]
QED

Theorem replace_memory_entry_type:
  replace_memory_entry entry path v = INL entry' ==> entry'.type = entry.type
Proof
  rw[replace_memory_entry_def, AllCaseEqs()] >> simp[scope_entry_accfupds]
QED

Theorem replace_memory_entry_value_type:
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  subscripts_type entry.type path = SOME ptv /\ value_has_type ptv v /\
  replace_memory_entry entry path v = INL entry' ==>
  value_has_type entry'.type entry'.value
Proof
  rw[replace_memory_entry_def, AllCaseEqs()] >>
  gvs[scope_entry_accfupds] >>
  metis_tac[assign_subscripts_replace_type_metadata]
QED


Theorem record_pop_history_typed:
  popped_history_typed tv history /\ value_has_type tv old /\
  well_formed_type_value tv /\ evaluate_subscripts tv old path = INL arr /\
  popped_value arr = INL p ==>
  popped_history_typed tv (record_pop path arr p history)
Proof
  strip_tac >>
  `?ptv. subscripts_type tv path = SOME ptv /\
         well_formed_type_value ptv /\ value_has_type ptv arr` by
    metis_tac[evaluate_subscripts_declared_type_exists] >>
  Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  Cases_on `a` >> gvs[vyperValueOperationTheory.popped_value_def] >>
  Cases_on `ptv` >> gvs[value_has_type_def] >>
  Cases_on `b` >> gvs[value_has_type_def, well_formed_type_value_def] >>
  irule record_pop_history_typed_at_path >>
  goal_assum (drule_at Any) >>
  simp[value_has_type_def, vyperValueOperationTheory.popped_value_def] >>
  metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place boundary: " ^ name ^ "\n")
     else raise Fail ("Incomplete place boundary: " ^ name)
  end) (DB.thms "vyperPlaceStatePreservation");
