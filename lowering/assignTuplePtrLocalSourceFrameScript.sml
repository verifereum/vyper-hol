(* Source-only frames, independent of the destination representation. *)
Theory assignTuplePtrLocalSourceFrame
Ancestors
  tupleTargetStoreProps vyperInterpreter vyperState vyperValue vyperLookup
  list finite_map

Theorem tuple_local_success_entry_ptr[local]:
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') ==>
  ?entry. lookup_scopes id es.scopes = SOME entry /\ entry.assignable
Proof
  simp[evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, get_place_def, get_scopes_def] >>
  Cases_on `lookup_scopes id es.scopes` >>
  simp[raise_def, bind_def] >>
  strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  gvs[get_place_def, return_def, write_place_def, get_scopes_def,
      bind_def, lift_option_type_def, type_check_def, assert_def] >>
  Cases_on `x.assignable` >>
  gvs[assert_def, return_def, raise_def, bind_def, ignore_bind_def]
QED

Theorem tuple_local_assignment_scope_frame_ptr:
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') ==>
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
       OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes))
Proof
  strip_tac >> drule tuple_local_success_entry_ptr >> strip_tac >>
  drule_all tuple_target_local_assignment >> strip_tac >> gvs[] >>
  conj_tac
  >- (drule tuple_target_local_domain_frame >>
      disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  drule tuple_target_local_preserves_layout >> simp[]
QED
