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

Theorem read_memory_path_type:
  value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\
  popped_history_typed entry.type entry.popped /\
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v ==> value_has_type ptv v
Proof
  rw[read_memory_path_def, AllCaseEqs()] >>
  metis_tac[evaluate_subscripts_type, read_popped_type]
QED

Theorem scope_history_typed_update:
  scope_history_typed sc /\ popped_history_typed entry.type entry.popped ==>
  scope_history_typed (sc |+ (id,entry))
Proof
  rw[scope_history_typed_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem push_scope_history_typed:
  state_history_typed st /\ push_scope st = (res,st') ==>
  state_history_typed st'
Proof
  rw[push_scope_def, return_def, state_history_typed_def] >>
  gvs[evaluation_state_accfupds]
QED

Theorem pop_scope_history_typed:
  state_history_typed st /\ pop_scope st = (res,st') ==>
  state_history_typed st'
Proof
  Cases_on `st.scopes` >>
  gvs[pop_scope_def, return_def, raise_def, state_history_typed_def,
      evaluation_state_accfupds] >> rpt strip_tac >> gvs[evaluation_state_accfupds]
QED

Theorem push_scope_with_var_history_typed:
  state_history_typed st /\ push_scope_with_var id tv v st = (res,st') ==>
  state_history_typed st'
Proof
  rw[push_scope_with_var_def, return_def, state_history_typed_def] >>
  gvs[evaluation_state_accfupds] >>
  irule scope_history_typed_update >> simp[]
QED

Theorem new_variable_history_typed:
  state_history_typed st /\ new_variable id tv v st = (res,st') ==>
  state_history_typed st'
Proof
  Cases_on `st.scopes` >>
  rw[new_variable_def, bind_def, ignore_bind_def, return_def, raise_def,
     get_scopes_def, set_scopes_def, type_check_def, assert_def, AllCaseEqs(),
     state_history_typed_def] >>
  gvs[evaluation_state_accfupds] >> irule scope_history_typed_update >> simp[]
QED

Theorem state_history_typed_scopes:
  state_history_typed st /\ st'.scopes = st.scopes ==> state_history_typed st'
Proof
  simp[state_history_typed_def]
QED

Theorem set_immutable_history_typed:
  state_history_typed st /\ set_immutable cx src id tv v st = (res,st') ==>
  state_history_typed st'
Proof
  metis_tac[state_history_typed_scopes,
    vyperScopePreservationTheory.set_immutable_scopes]
QED

Theorem write_storage_slot_history_typed:
  state_history_typed st /\ write_storage_slot cx tr slot tv v st = (res,st') ==>
  state_history_typed st'
Proof
  metis_tac[state_history_typed_scopes,
    vyperScopePreservationTheory.write_storage_slot_scopes]
QED

Theorem set_scopes_history_typed:
  EVERY scope_history_typed scopes /\ set_scopes scopes st = (res,st') ==>
  state_history_typed st'
Proof
  rw[set_scopes_def, return_def, state_history_typed_def] >>
  simp[evaluation_state_accfupds]
QED

Theorem record_pop_history_typed_at_path:
  popped_history_typed tv history /\
  subscripts_type tv path = SOME (ArrayTV etv (Dynamic n)) /\
  well_formed_type_value etv /\
  value_has_type (ArrayTV etv (Dynamic n)) arr /\
  evaluate_subscripts tv old path = INL arr /\ popped_value arr = INL p ==>
  popped_history_typed tv (record_pop tv old path p history)
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

Theorem replace_memory_entry_history_typed:
  popped_history_typed entry.type entry.popped /\
  replace_memory_entry entry path v = INL entry' ==>
  popped_history_typed entry'.type entry'.popped
Proof
  rw[replace_memory_entry_def, AllCaseEqs()] >>
  simp[scope_entry_accfupds]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place boundary: " ^ name ^ "\n")
     else raise Fail ("Incomplete place boundary: " ^ name)
  end) (DB.thms "vyperPlaceStatePreservation");
