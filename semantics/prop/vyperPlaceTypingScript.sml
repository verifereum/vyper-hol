Theory vyperPlaceTyping
Ancestors
  list option pair finite_map vyperMisc vyperState vyperTyping vyperTypeInvariants
  vyperTypeEnv vyperStatePreservation vyperTypeStatePreservation vyperPlaceInvariants
  vyperPlaceStatePreservation vyperPlaceFrames

Definition runtime_place_typed_def:
  runtime_place_typed cx st p tv <=>
    well_formed_type_value tv /\
    place_type_value cx p st = (INL tv,st)
End

Theorem runtime_place_typed_storage[simp]:
  runtime_place_typed cx st (StoragePlace tr slot ptv) tv <=>
    tv = ptv /\ well_formed_type_value tv
Proof
  simp[runtime_place_typed_def, place_type_value_def, return_def] >> metis_tac[]
QED

Theorem runtime_place_typed_memory:
  runtime_place_typed cx st (MemoryPlace id path) tv <=>
    well_formed_type_value tv /\
    ?entry. lookup_scopes id st.scopes = SOME entry /\
      subscripts_type entry.type path = SOME tv
Proof
  Cases_on `lookup_scopes id st.scopes` >>
  simp[runtime_place_typed_def, place_type_value_def, get_scopes_def,
       bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `subscripts_type x.type path` >>
  simp[return_def, raise_def] >> metis_tac[]
QED

Theorem runtime_place_typed_immutable:
  runtime_place_typed cx st (ImmutablePlace src id path) tv <=>
    well_formed_type_value tv /\
    ?imms root a. get_immutables cx src st = (INL imms,st) /\
      FLOOKUP imms id = SOME (root,a) /\ subscripts_type root path = SOME tv
Proof
  simp[runtime_place_typed_def, place_type_value_def, bind_def,
       lift_option_type_def, option_CASE_rator, return_def, raise_def,
       AllCaseEqs(), pairTheory.EXISTS_PROD] >>
  eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem read_place_preserves_state:
  read_place cx p st = (res,st') ==> st' = st
Proof
  metis_tac[read_place_state, SND]
QED

Theorem get_immutables_success_typed:
  state_well_typed st /\ get_immutables cx src st = (INL imms,st') /\
  FLOOKUP imms id = SOME (tv,v) ==>
    value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[get_immutables_def, get_address_immutables_def, bind_def,
     lift_option_type_def, option_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  gvs[] >> metis_tac[state_well_typed_immutables_ALOOKUP,
            imms_well_typed_get_source_immutables]
QED

Theorem lookup_scopes_well_typed_type:
  !scopes id entry. EVERY scope_well_typed scopes /\
    lookup_scopes id scopes = SOME entry ==> well_formed_type_value entry.type
Proof
  Induct >> simp[lookup_scopes_def] >> rpt gen_tac >>
  Cases_on `FLOOKUP h id` >> simp[] >>
  metis_tac[scope_well_typed_def]
QED

Theorem read_place_success_type:
  place_state_well_typed st /\ runtime_place_typed cx st p tv /\
  read_place cx p st = (INL v,st') ==> value_has_type tv v
Proof
  Cases_on `p`
  >- (simp[runtime_place_typed_storage, read_place_def] >>
      metis_tac[read_storage_slot_success_type])
  >- (rw[runtime_place_typed_memory, read_place_def, bind_def,
         get_scopes_def, lift_option_type_def, lift_sum_def,
         return_def, raise_def, AllCaseEqs()] >>
      gvs[place_state_well_typed_def, state_well_typed_def,
          return_def, raise_def, sum_CASE_rator, AllCaseEqs()] >>
      irule read_memory_path_type >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      metis_tac[lookup_scopes_well_typed_value_has_type,
                lookup_scopes_history_typed, state_history_typed_def,
                lookup_scopes_well_typed_type]) >>
  rw[runtime_place_typed_immutable, read_place_def, bind_def,
     lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[place_state_well_typed_def, return_def, raise_def,
      sum_CASE_rator, AllCaseEqs()] >>
  drule_all get_immutables_success_typed >> strip_tac >>
  irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem struct_field_slot_type:
  !fields id off tv. struct_field_slot fields id = SOME (off,tv) ==>
    ALOOKUP fields id = SOME tv
Proof
  Induct >> simp[struct_field_slot_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC >> simp[] >>
  Cases_on `struct_field_slot fields id` >> simp[] >>
  Cases_on `x` >> simp[] >> metis_tac[]
QED

Theorem struct_field_slot_offset:
  !fields id off tv. struct_field_slot fields id = SOME (off,tv) ==>
    ?pre post. fields = pre ++ (id,tv)::post /\
      off = SUM (MAP (type_slot_size o SND) pre) /\
      ~MEM id (MAP FST pre)
Proof
  Induct >> simp[struct_field_slot_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC
  >- (rw[] >> qexistsl_tac [`[]`,`fields`] >> simp[]) >>
  Cases_on `struct_field_slot fields id` >> simp[] >>
  Cases_on `x` >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`(q,r)::pre`,`post`] >> simp[]
QED

Theorem extend_storage_place_type:
  well_formed_type_value tv /\ subscript_type tv sb = SOME etv /\
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
    runtime_place_typed cx st' p etv
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[subscript_type_def, extend_storage_place_def, raise_def] >>
  TRY (rename1 `ValueSubscript v` >> Cases_on `v` >>
       simp[subscript_type_def, extend_storage_place_def, raise_def]) >>
  rpt strip_tac >> gvs[] >>
  all_tac >~ [`well_formed_type_value (StructTV fields)`]
  >- (gvs[bind_def, lift_option_type_def, return_def, raise_def,
           AllCaseEqs()] >>
      Cases_on `struct_field_slot fields s` >> gvs[return_def, raise_def] >>
      PairCases_on `x` >> gvs[return_def] >>
      drule struct_field_slot_type >> strip_tac >> gvs[] >>
      irule subscript_type_well_formed >>
      qexistsl_tac [`AttrSubscript s`,`StructTV fields`] >>
      simp[subscript_type_def]) >>
  all_tac >~ [`well_formed_type_value (TupleTV tvs)`]
  >- (gvs[bind_def, ignore_bind_def, check_def, assert_def,
          lift_option_type_def, return_def, raise_def, oEL_THM] >>
      irule subscript_type_well_formed >>
      qexistsl_tac [`ValueSubscript (IntV i)`, `TupleTV tvs`] >>
      simp[subscript_type_def]) >>
  Cases_on `b` >>
  gvs[resolve_array_element_def, bind_def, ignore_bind_def, check_def,
      assert_def, return_def, raise_def, get_storage_backend_def,
      get_accounts_def, get_transient_storage_def, lift_option_def,
      AllCaseEqs(), well_formed_type_value_def] >>
  Cases_on `etv` >> gvs[resolve_array_element_def, return_def]
QED

Theorem extend_memory_place_type:
  (!tr slot ptv. p <> StoragePlace tr slot ptv) /\
  runtime_place_typed cx st p tv /\ subscript_type tv sb = SOME etv ==>
    runtime_place_typed cx st (extend_memory_place p sb) etv
Proof
  Cases_on `p` >>
  simp[extend_memory_place_def, runtime_place_typed_memory,
       runtime_place_typed_immutable, subscripts_type_append,
       subscripts_type_def] >>
  rpt strip_tac >>
  TRY (drule_all subscript_type_well_formed >> simp[] >> NO_TAC) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extend_place_typed:
  runtime_place_typed cx st p tv /\ subscript_type tv sb = SOME etv /\
  extend_place cx input_tv (PlaceR p) sb st = (INL (PlaceR q),st') ==>
    runtime_place_typed cx st' q etv
Proof
  Cases_on `p`
  >- (simp[extend_place_def, runtime_place_typed_storage] >>
      rpt strip_tac >>
      gvs[bind_def, return_def, AllCaseEqs()] >>
      metis_tac[extend_storage_place_type]) >>
  rpt strip_tac >>
  `st' = st` by metis_tac[vyperPlaceFramesTheory.extend_place_state, SND] >>
  gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
      lift_sum_def, raise_def, AllCaseEqs()] >>
  irule extend_memory_place_type >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem extend_array_ref_typed:
  well_formed_type_value (ArrayTV etv bd) /\
  subscript_type (ArrayTV etv bd) sb = SOME leaf_tv /\
  extend_place cx input_tv (ValueR (ArrayRef tr slot etv bd)) sb st =
    (INL (PlaceR q),st') ==> runtime_place_typed cx st' q leaf_tv
Proof
  simp[extend_place_def] >> rpt strip_tac >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  metis_tac[extend_storage_place_type]
QED

Theorem write_memory_place_history_typed:
  state_history_typed st /\
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  state_history_typed st'
Proof
  strip_tac >> Cases_on `find_containing_scope id st.scopes` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      return_def, raise_def] >> PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry x2 path v` >>
  gvs[return_def, raise_def] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  gvs[state_history_typed_def, EVERY_APPEND] >>
  irule scope_history_typed_update >> simp[] >>
  irule replace_memory_entry_history_typed >>
  goal_assum (drule_at Any) >>
  metis_tac[scope_history_typed_def]
QED

Theorem write_place_history_typed:
  state_history_typed st /\ write_place cx p v st = (res,st') ==>
  state_history_typed st'
Proof
  Cases_on `p` >>
  metis_tac[write_memory_place_history_typed, state_history_typed_scopes,
            write_storage_place_scopes, write_immutable_place_scopes]
QED

Theorem write_memory_place_preserves_state_well_typed:
  state_well_typed st /\ runtime_place_typed cx st (MemoryPlace id path) tv /\
  value_has_type tv v /\ write_place cx (MemoryPlace id path) v st = (res,st') ==>
  state_well_typed st'
Proof
  rw[runtime_place_typed_memory] >>
  Cases_on `find_containing_scope id st.scopes` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      return_def, raise_def] >> PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry x2 path v` >> gvs[return_def, raise_def] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >>
  gvs[state_well_typed_def, EVERY_APPEND] >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[scope_well_typed_def] >>
  `value_has_type entry'.type entry'.value` by
    (drule_all replace_memory_entry_value_type >> simp[]) >>
  `entry'.type = entry.type` by metis_tac[replace_memory_entry_type] >>
  rw[scope_well_typed_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[scope_well_typed_def]
QED

Theorem write_immutable_place_preserves_state_well_typed:
  state_well_typed st /\ runtime_place_typed cx st (ImmutablePlace src id path) tv /\
  value_has_type tv v /\ write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  state_well_typed st'
Proof
  rw[runtime_place_typed_immutable] >>
  `value_has_type root a /\ well_formed_type_value root` by
    metis_tac[get_immutables_success_typed] >>
  gvs[write_place_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `assign_subscripts root a path (Replace v)` >>
  gvs[return_def, raise_def] >>
  irule set_immutable_preserves_state_well_typed >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[assign_subscripts_replace_type_metadata]
QED

Theorem write_place_preserves_state_well_typed:
  state_well_typed st /\ runtime_place_typed cx st p tv /\
  value_has_type tv v /\ write_place cx p v st = (res,st') ==>
  state_well_typed st'
Proof
  Cases_on `p`
  >- (simp[write_place_def] >>
      metis_tac[write_storage_slot_preserves_state_well_typed_any]) >>
  metis_tac[write_memory_place_preserves_state_well_typed,
            write_immutable_place_preserves_state_well_typed]
QED

Theorem write_place_preserves_place_state_well_typed:
  place_state_well_typed st /\ runtime_place_typed cx st p tv /\
  value_has_type tv v /\ write_place cx p v st = (res,st') ==>
  place_state_well_typed st'
Proof
  simp[place_state_well_typed_def] >>
  metis_tac[write_place_history_typed, write_place_preserves_state_well_typed]
QED

Theorem lookup_scopes_update_type[local]:
  !pre sc id entry entry' rest other.
  FLOOKUP sc id = SOME entry /\ entry'.type = entry.type ==>
  OPTION_MAP (\e. e.type) (lookup_scopes other (pre ++ (sc |+ (id,entry'))::rest)) =
  OPTION_MAP (\e. e.type) (lookup_scopes other (pre ++ sc::rest))
Proof
  Induct >> simp[lookup_scopes_def] >> rpt gen_tac
  >- (strip_tac >> Cases_on `other = id` >> gvs[FLOOKUP_UPDATE]) >>
  Cases_on `FLOOKUP h other` >> simp[]
QED

Theorem write_memory_place_lookup_type:
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  !other. OPTION_MAP (\e. e.type) (lookup_scopes other st'.scopes) =
          OPTION_MAP (\e. e.type) (lookup_scopes other st.scopes)
Proof
  strip_tac >> Cases_on `find_containing_scope id st.scopes` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      return_def, raise_def] >> PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry x2 path v` >> gvs[return_def, raise_def] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> gen_tac >>
  irule lookup_scopes_update_type >>
  metis_tac[replace_memory_entry_type]
QED

Theorem write_memory_place_preserves_runtime_place_type:
  runtime_place_typed cx st (MemoryPlace other other_path) tv /\
  write_place cx (MemoryPlace id path) v st = (res,st') ==>
  runtime_place_typed cx st' (MemoryPlace other other_path) tv
Proof
  rw[runtime_place_typed_memory] >>
  drule write_memory_place_lookup_type >> disch_then (qspec_then `other` mp_tac) >>
  Cases_on `lookup_scopes other st'.scopes` >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem set_immutable_lookup_written:
  set_immutable cx src id tv v st = (INL u,st') ==>
  ?imms. get_immutables cx src st' = (INL imms,st') /\
         FLOOKUP imms id = SOME (tv,v)
Proof
  rw[set_immutable_def, get_address_immutables_def, bind_def,
     lift_option_type_def, lift_option_def, set_address_immutables_def,
     return_def, raise_def, AllCaseEqs(), LET_THM] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  simp[get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, return_def, raise_def,
       set_source_immutables_def, get_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `src` >> simp[get_source_immutables_def,
                         set_source_immutables_def,
                         alistTheory.ALOOKUP_ADELKEY, FLOOKUP_UPDATE]
QED

Theorem write_immutable_place_root_type:
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (root,a) /\
  write_place cx (ImmutablePlace src id path) v st = (INL u,st') ==>
  ?imms' new. get_immutables cx src st' = (INL imms',st') /\
             FLOOKUP imms' id = SOME (root,new)
Proof
  rw[write_place_def, bind_def, lift_option_type_def, lift_sum_def,
     return_def, raise_def, AllCaseEqs()] >>
  Cases_on `assign_subscripts root a path (Replace v)` >>
  gvs[return_def, raise_def] >>
  drule set_immutable_lookup_written >> metis_tac[]
QED

Theorem write_immutable_place_preserves_runtime_place_type:
  runtime_place_typed cx st (ImmutablePlace src id other_path) tv /\
  write_place cx (ImmutablePlace src id path) v st = (INL u,st') ==>
  runtime_place_typed cx st' (ImmutablePlace src id other_path) tv
Proof
  rw[runtime_place_typed_immutable] >>
  drule_all write_immutable_place_root_type >> strip_tac >>
  metis_tac[]
QED

Theorem set_immutable_lookup_other:
  other <> id /\ get_immutables cx src st = (INL imms,st) /\
  set_immutable cx src id tv v st = (INL u,st') ==>
  ?imms'. get_immutables cx src st' = (INL imms',st') /\
          FLOOKUP imms' other = FLOOKUP imms other
Proof
  rw[get_immutables_def, set_immutable_def, get_address_immutables_def,
     bind_def, lift_option_type_def, lift_option_def, set_address_immutables_def,
     return_def, raise_def, AllCaseEqs(), LET_THM] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  simp[get_address_immutables_def, bind_def,
       lift_option_type_def, return_def, raise_def,
       set_source_immutables_def, get_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `src` >> simp[get_source_immutables_def,
                         set_source_immutables_def,
                         alistTheory.ALOOKUP_ADELKEY, FLOOKUP_UPDATE]
QED

Theorem write_immutable_place_preserves_other_runtime_place_type:
  other <> id /\ runtime_place_typed cx st (ImmutablePlace src other other_path) tv /\
  write_place cx (ImmutablePlace src id path) v st = (INL u,st') ==>
  runtime_place_typed cx st' (ImmutablePlace src other other_path) tv
Proof
  rw[runtime_place_typed_immutable] >>
  gvs[write_place_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP imms id` >> gvs[return_def, raise_def] >>
  Cases_on `assign_subscripts (FST tva) (SND tva) path (Replace v)` >>
  gvs[return_def, raise_def] >>
  drule_all set_immutable_lookup_other >> strip_tac >> metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place typing: " ^ name ^ "\n")
     else raise Fail ("Incomplete place typing: " ^ name)
  end) (DB.thms "vyperPlaceTyping");
