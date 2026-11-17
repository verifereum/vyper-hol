(* The source update, independent of the compiled-store proof cone. *)
Theory placeMemoryEntryUpdate
Ancestors
  vyperState vyperLookup finite_map list pair

Theorem write_memory_place_entry_update:
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?entry entry'.
    lookup_scopes id ee.scopes = SOME entry /\
    replace_memory_entry entry path v = INL entry' /\
    lookup_scopes id ff.scopes = SOME entry' /\
    (!n. n <> id ==> lookup_scopes n ff.scopes = lookup_scopes n ee.scopes) /\
    ff = ee with scopes := ff.scopes
Proof
  simp[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
       lift_option_def, lift_sum_def, type_check_def, assert_def,
       set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `find_containing_scope id ee.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x` >>
  gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def,
      lift_sum_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `replace_memory_entry x2 path v` >> gvs[return_def, raise_def] >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  qexistsl_tac [`x2`, `entry'`] >>
  simp[lookup_scopes_update, lookup_scopes_update_other]
QED
