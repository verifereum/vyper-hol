Theory bodySimAugPlaceMemory
Ancestors
  vyperState vyperMisc vyperPlaceStatePreservation list pair sum

Theorem aug_place_subscripts_append_live:
  !path tv a ptv v sb w.
    subscripts_type tv path = SOME ptv /\
    evaluate_subscripts tv a path = INL v /\
    evaluate_subscripts ptv v [sb] = INL w ==>
    evaluate_subscripts tv a (path ++ [sb]) = INL w
Proof
  Induct >> simp[subscripts_type_def, evaluate_subscripts_def] >>
  rpt gen_tac >>
  simp[subscripts_type_def, AllCaseEqs()] >> strip_tac >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `a`] assume_tac) >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path ++ [sb]`, `a`] SUBST1_TAC) >>
  Cases_on `evaluate_subscripts tv a [h]` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_extend_memory_live:
  !cx id path entry v sb s q s'.
    lookup_scopes id s.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    extend_place cx (PlaceR (MemoryPlace id path)) sb s = (INL q,s') ==>
    ?entry' w. q = PlaceR (MemoryPlace id (path ++ [sb])) /\
      lookup_scopes id s'.scopes = SOME entry' /\
      evaluate_subscripts entry'.type entry'.value (path ++ [sb]) = INL w
Proof
  rpt strip_tac >>
  gvs[extend_place_def, place_type_value_def, read_place_def,
      read_memory_path_def, get_scopes_def, bind_def, ignore_bind_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def,
      extend_memory_place_def, AllCaseEqs()] >>
  gvs[option_CASE_rator, sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[aug_place_subscripts_append_live]
QED

Theorem aug_place_extend_storage_not_memory[local]:
  !tv sb cx tr slot s id path s'.
    extend_storage_place cx tr slot tv sb s =
      (INL (MemoryPlace id path),s') ==> F
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >> Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[prod_CASE_rator, return_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def]) >>
  Cases_on `tv` >>
  simp[extend_storage_place_def, bind_def, ignore_bind_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[prod_CASE_rator, return_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def]
QED

Theorem aug_place_extend_memory_inversion:
  !pv sb cx s id path s'.
    extend_place cx pv sb s = (INL (PlaceR (MemoryPlace id path)),s') ==>
    ?old. pv = PlaceR (MemoryPlace id old) /\ path = old ++ [sb]
Proof
  Cases
  >- simp[extend_place_def, raise_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def,
           extend_memory_place_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      metis_tac[aug_place_extend_storage_not_memory]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, ignore_bind_def,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_type_CASE_rator, bind_def, return_def, raise_def,
      AllCaseEqs()]
QED
