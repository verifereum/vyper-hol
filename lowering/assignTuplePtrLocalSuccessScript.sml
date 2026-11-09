(* Source-only inversion; repeated destination names are permitted. *)
Theory assignTuplePtrLocalSuccess
Ancestors
  tupleLocalStoreProps tupleTargetStoreProps vyperLookup vyperInterpreter
  vyperState vyperValue list finite_map
Libs
  monadsyntax

Theorem tuple_local_success_assignable_ptr:
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v ee = (INL (),ee') ==>
  ?entry. lookup_scopes id ee.scopes = SOME entry /\ entry.assignable
Proof
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[bind_def, get_scopes_def, get_place_def, type_check_def,
       assert_def, return_def, raise_def, ignore_bind_def] >>
  Cases_on `lookup_scopes id ee.scopes` >> simp[] >> strip_tac >>
  gvs[get_place_def, return_def] >>
  `var_assignable ee id` by
    (irule write_memory_place_implies_var_assignable >>
     qexistsl_tac [`cx`, `[]`, `v`] >> simp[]) >>
  gvs[var_assignable_def, lookup_name_typed_def]
QED

Theorem tuple_locals_success_initial_assignable_ptr:
  !ids cx vs ee ee'.
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs ee = (INL (),ee') ==>
    EVERY (\id. ?entry. lookup_scopes id ee.scopes = SOME entry /\ entry.assignable) ids
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def] >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx (BaseTarget (NameTarget h)) h' ee` >>
  Cases_on `q` >> simp[] >> strip_tac >> Cases_on `x` >> gvs[] >>
  `?entry. lookup_scopes h ee.scopes = SOME entry /\ entry.assignable` by
    metis_tac[tuple_local_success_assignable_ptr] >> simp[] >>
  first_x_assum drule >> strip_tac >>
  drule assign_tuple_target_local >> simp[] >> strip_tac >> gvs[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule tuple_target_local_preserves_layout >>
  disch_then (qspecl_then [`h'`, `id`] mp_tac) >>
  Cases_on `lookup_scopes id ee.scopes` >> simp[] >> metis_tac[]
QED
