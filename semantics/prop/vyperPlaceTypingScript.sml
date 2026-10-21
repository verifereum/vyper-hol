Theory vyperPlaceTyping
Ancestors
  list option pair finite_map vyperMisc vyperState vyperTyping vyperTypeInvariants
  vyperTypeEnv vyperStatePreservation vyperTypeStatePreservation vyperPlaceInvariants
  vyperPlaceStatePreservation

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

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then print ("Kernel-closed place typing: " ^ name ^ "\n")
     else raise Fail ("Incomplete place typing: " ^ name)
  end) (DB.thms "vyperPlaceTyping");
